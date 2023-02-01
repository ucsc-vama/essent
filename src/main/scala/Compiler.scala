package essent

import java.io.{File, FileWriter, Writer}

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency
import firrtl.stage.transforms

import logger._


class EssentEmitter(initialOpt: OptFlags, w: Writer) extends LazyLogging {
  val flagVarName = "PARTflags"
  val actVarName = "ACTcounts"
  val sigTrackName = "SIGcounts"
  val sigActName = "SIGact"
  val sigExtName = "SIGext"
  var sigNameToID = Map[String,Int]()
  implicit val rn = new Renamer


  // Declaring Modules
  //----------------------------------------------------------------------------
  def declareModule(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regName = d.name
      Seq(s"$typeStr $regName;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${m.name}[${m.depth}];"
    }}
    val modulesAndPrefixes = findModuleInstances(m.body)
    val moduleDecs = modulesAndPrefixes map { case (module, fullName) => {
      val instanceName = fullName.split("\\.").last
      s"$module $instanceName;"
    }}
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, registerDecs)
    w.writeLines(1, memDecs)
    w.writeLines(1, m.ports flatMap emitPort(modName == topName))
    w.writeLines(1, moduleDecs)
    w.writeLines(0, "")
    w.writeLines(1, s"$modName() {")
    w.writeLines(2, initializeVals(modName == topName)(m, registers, memories))
    w.writeLines(1, "}")
    if (modName == topName) {
      w.writeLines(0, "")
      // w.writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
    } else {
      w.writeLines(0, s"} $modName;")
    }
  }

  def declareExtModule(m: ExtModule) {
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, m.ports flatMap emitPort(true))
    w.writeLines(0, s"} $modName;")
  }


  // Write General-purpose Eval
  //----------------------------------------------------------------------------
  // TODO: move specialized CondMux emitter elsewhere?
  def writeBodyInner(indentLevel: Int, sg: StatementGraph, opt: OptFlags,
                     keepAvail: Set[String] = Set()) {
    // ng.stmtsOrdered foreach { stmt => w.writeLines(indentLevel, emitStmt(stmt)) }
    if (opt.conditionalMuxes)
      MakeCondMux(sg, rn, keepAvail)
    val noMoreMuxOpts = opt.copy(conditionalMuxes = false)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          w.writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        w.writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), noMoreMuxOpts)
        w.writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), noMoreMuxOpts)
        w.writeLines(indentLevel, "}")
      }
      case _ => {
        w.writeLines(indentLevel, emitStmt(stmt))
        if (opt.withVCD) {
          stmt match {
          case mw: MemWrite =>
          case _ => 
            val resultName = findResultName(stmt)
            resultName match {
              case Some(name) =>
              val cleanName = rn.removeDots(name)
              if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
                if(!cleanName.contains("$_") && !cleanName.contains("$next") && !cleanName.startsWith("_")) {
                  w.writeLines(indentLevel, s"""if( (cycle_count == 0) || ($cleanName != ${cleanName}_old)) { outfile << $cleanName.to_bin_str(); outfile << "!$cleanName" << "\\n";} """)
                  w.writeLines(indentLevel, s""" ${cleanName}_old = $cleanName;""")
              }
              }
            case None =>
            }
          }
        }
        if (opt.trackSigs) emitSigTracker(stmt, indentLevel, opt)
      }
    }}
  }

  def writeRegResetOverrides(sg: StatementGraph) {
    val updatesWithResets = sg.allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    assert(updatesWithResets.isEmpty)
//    val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
//    val overridesToWrite = resetGroups.toSeq flatMap {
//      case (resetName, regDefs) => {
//        val body = regDefs map {
//          r => s"$tabs${rn.emit(r.name)} = ${emitExpr(r.init)};"
//        }
//        Seq(s"if ($resetName) {") ++ body ++ Seq("}")
//      }
//    }
//    if (overridesToWrite.nonEmpty) {
//      w.writeLines(2, "if (update_registers) {")
//      // FUTURE: will overrides need triggers if partitioned?
//      w.writeLines(3, overridesToWrite)
//      w.writeLines(2, "}")
//    }
  }


  // Write Zoning Optimized Eval
  //----------------------------------------------------------------------------
  def genEvalFuncName(partID: Int): String = "EVAL_" + partID

  def genDepPartTriggers(consumerIDs: Seq[Int], condition: String): Seq[String] = {
    consumerIDs.sorted map { consumerID => s"$flagVarName[$consumerID] |= $condition;" }
  }

  def genAllTriggers(signalNames: Seq[String], outputConsumers: Map[String, Seq[Int]],
      suffix: String): Seq[String] = {
    selectFromMap(signalNames, outputConsumers).toSeq flatMap { case (name, consumerIDs) => {
      genDepPartTriggers(consumerIDs, s"${rn.emit(name)} != ${rn.emit(name + suffix)}")
    }}
  }

  def writeZoningPredecs(
                          sg: StatementGraph,
                          condPartWorker: MakeCondPart,
                          topName: String,
                          extIOtypes: Map[String, Type],
                          opt: OptFlags) {
    // predeclare part outputs
    val outputPairs = condPartWorker.getPartOutputsToDeclare()
    val outputConsumers = condPartWorker.getPartInputMap()
    w.writeLines(1, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name)};"})
    val extIOCacheDecs = condPartWorker.getExternalPartInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)};"
    }
    w.writeLines(1, extIOCacheDecs)
    w.writeLines(1, s"std::array<bool,${condPartWorker.getNumParts()}> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    w.writeLines(1, s"bool sim_cached = false;")
    w.writeLines(1, s"bool regs_set = false;")
    w.writeLines(1, s"bool update_registers;")
    w.writeLines(1, s"bool done_reset;")
    w.writeLines(1, s"bool verbose;")
    w.writeLines(0, "")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        w.writeLines(1, s"void ${genEvalFuncName(cp.id)}() {")
        if (!cp.alwaysActive)
          w.writeLines(2, s"$flagVarName[${cp.id}] = false;")
        if (opt.trackParts)
          w.writeLines(2, s"$actVarName[${cp.id}]++;")

        val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
        w.writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
        writeBodyInner(2, StatementGraph(noRegUpdates), opt, keepAvail)
        w.writeLines(2, genAllTriggers(cp.outputsToDeclare.keys.toSeq, outputConsumers, condPartWorker.cacheSuffix))
        val regUpdateNamesInPart = regUpdates flatMap findResultName
        w.writeLines(2, genAllTriggers(regUpdateNamesInPart, outputConsumers, "$next"))
        // triggers for MemWrites
        val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }
        val memWriteTriggers = memWritesInPart flatMap { mw => {
          val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
          genDepPartTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
        }}
        w.writeLines(2, memWriteTriggers)
        w.writeLines(2, regUpdates flatMap emitStmt)

        w.writeLines(1, "}")
      }
      case _ => throw new Exception(s"Statement at top-level is not a CondPart (${stmt.serialize})")
    }}
    w.writeLines(0, "")
  }

  def writeZoningBody(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags) {
    w.writeLines(2, "if (reset || !done_reset) {")
    w.writeLines(3, "sim_cached = false;")
    w.writeLines(3, "regs_set = false;")
    w.writeLines(2, "}")
    w.writeLines(2, "if (!sim_cached) {")
    w.writeLines(3, s"$flagVarName.fill(true);")
    w.writeLines(2, "}")
    w.writeLines(2, "sim_cached = regs_set;")
    w.writeLines(2, "this->update_registers = update_registers;")
    w.writeLines(2, "this->done_reset = done_reset;")
    w.writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    w.writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    w.writeLines(2, extIOCaches.toSeq)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        if (!cp.alwaysActive)
          w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
        else
          w.writeLines(2, s"${genEvalFuncName(cp.id)}();")
      }
      case _ => w.writeLines(2, emitStmt(stmt))
    }}
    // w.writeLines(2,  "#ifdef ALL_ON")
    // w.writeLines(2, s"$flagVarName.fill(true);" )
    // w.writeLines(2,  "#endif")
    w.writeLines(2, "regs_set = true;")
  }


  def declareSigTracking(sg: StatementGraph, topName: String, opt: OptFlags) {
    val allNamesAndTypes = sg.collectValidStmts(sg.nodeRange) flatMap findStmtNameAndType
    sigNameToID = (allNamesAndTypes map { _._1 }).zipWithIndex.toMap
    w.writeLines(0, "")
    w.writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigTrackName{};")
    if (opt.trackExts) {
      w.writeLines(0, s"std::array<bool,${sigNameToID.size}> $sigActName{};")
      w.writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigExtName{};")
    }
    w.writeLines(0, "namespace old {")
    w.writeLines(1, allNamesAndTypes map {
      case (name, tpe) => s"${genCppType(tpe)} ${name.replace('.','$')};"
    })
    w.writeLines(0, "}")
  }

  def emitSigTracker(stmt: Statement, indentLevel: Int, opt: OptFlags) {
    stmt match {
      case mw: MemWrite =>
      case _ => {
        val resultName = findResultName(stmt)
        resultName match {
          case Some(name) => {
            val cleanName = name.replace('.','$')
            w.writeLines(indentLevel, s"$sigTrackName[${sigNameToID(name)}] += $name != old::$cleanName ? 1 : 0;")
            if (opt.trackExts) {
              w.writeLines(indentLevel, s"$sigActName[${sigNameToID(name)}] = $name != old::$cleanName;")
              val depNames = findDependencesStmt(stmt).head.deps
              val trackedDepNames = depNames filter sigNameToID.contains
              val depTrackers = trackedDepNames map {name => s"$sigActName[${sigNameToID(name)}]"}
              val anyDepActive = depTrackers.mkString(" || ")
              if (anyDepActive.nonEmpty)
                w.writeLines(indentLevel, s"$sigExtName[${sigNameToID(name)}] += !$sigActName[${sigNameToID(name)}] && ($anyDepActive) ? 1 : 0;")
            }
            w.writeLines(indentLevel, s"old::$cleanName = $name;")
          }
          case None =>
        }
      }
    }
  }

  def emitJsonWriter(opt: OptFlags, numParts: Int) {
    w.writeLines(0, "void writeActToJson() {")
    w.writeLines(1, "std::fstream file(\"activities.json\", std::ios::out | std::ios::binary);")
    w.writeLines(1, "JSON all_data;")
    if (opt.trackSigs) {
      w.writeLines(1, "JSON sig_acts;")
      w.writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      w.writeLines(2, s"""sig_acts[i] = JSON({"id", i, "acts", $sigTrackName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"signal-activities\"] = sig_acts;")
    }
    if (opt.trackParts) {
      w.writeLines(1, "JSON part_acts;")
      w.writeLines(1, s"for (int i=0; i<$numParts; i++) {")
      w.writeLines(2, s"""part_acts[i] = JSON({"id", i, "acts", $actVarName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"part-activities\"] = part_acts;")
    }
    if (opt.trackExts) {
      w.writeLines(1, "JSON sig_exts;")
      w.writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      w.writeLines(2, s"""sig_exts[i] = JSON({"id", i, "exts", $sigExtName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"sig-extinguishes\"] = sig_exts;")
    }
    w.writeLines(1, "all_data[\"cycles\"] = cycle_count;")
    w.writeLines(1, "file << all_data << std::endl;")
    w.writeLines(1, "file.close();")
    w.writeLines(0, "}")
  }


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute(circuit: Circuit) {
    val opt = initialOpt
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    w.writeLines(0, s"#ifndef $headerGuardName")
    w.writeLines(0, s"#define $headerGuardName")
    w.writeLines(0, "")
    w.writeLines(0, "#include <array>")
    w.writeLines(0, "#include <cstdint>")
    w.writeLines(0, "#include <cstdlib>")
    w.writeLines(0, "#include <uint.h>")
    w.writeLines(0, "#include <sint.h>")
    w.writeLines(0, "#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)")
    if (opt.trackParts || opt.trackSigs || opt.withVCD) {
      w.writeLines(0, "#include <fstream>")
      w.writeLines(0, "#include \"../SimpleJSON/json.hpp\"")
      w.writeLines(0, "using json::JSON;")
      w.writeLines(0, "uint64_t cycle_count = 0;")
    }
    val vcd = new Vcd(circuit,opt,w,rn)

    if(opt.withVCD) {
      w.writeLines(1, s"""std::ofstream outfile ("dump_$topName.vcd");""")
    }
    val sg = StatementGraph(circuit, opt.removeFlatConnects)
    logger.info(sg.makeStatsString)
    val containsAsserts = sg.containsStmtOfType[Stop]()
    val extIOMap = findExternalPorts(circuit)
    val condPartWorker = MakeCondPart(sg, rn, extIOMap)
    rn.populateFromSG(sg, extIOMap)
    if (opt.useCondParts) {
      condPartWorker.doOpt(opt.partCutoff)
    } else {
      if (opt.regUpdates)
        OptElideRegUpdates(sg)
    }
    // if (opt.trackSigs)
    //   declareSigTracking(sg, topName, opt)
    // if (opt.trackParts)
    //   w.writeLines(1, s"std::array<uint64_t,${sg.getNumParts()}> $actVarName{};")
    // if (opt.trackParts || opt.trackSigs)
   //    emitJsonWriter(opt, condPartWorker.getNumParts())
    // if (opt.partStats)
    //   sg.dumpPartInfoToJson(opt, sigNameToID)
    // if (opt.trackExts)
    //   sg.dumpNodeTypeToJson(sigNameToID)
    // sg.reachableAfter(sigNameToID)
    circuit.modules foreach {
      case m: Module => declareModule(m, topName)
      case m: ExtModule => declareExtModule(m)
    }
    val topModule = findModule(topName, circuit) match {case m: Module => m}
    if (initialOpt.writeHarness) {
      w.writeLines(0, "")
      w.writeLines(1, s"void connect_harness(CommWrapper<struct $topName> *comm) {")
      w.writeLines(2, HarnessGenerator.harnessConnections(topModule))
      w.writeLines(1, "}")
      w.writeLines(0, "")
    }
    if (opt.withVCD)  { vcd.declareOldvaluesAll(circuit) }
    if (containsAsserts) {
      w.writeLines(1, "bool assert_triggered = false;")
      w.writeLines(1, "int assert_exit_code;")
      w.writeLines(0, "")
    }
    if (opt.useCondParts)
      writeZoningPredecs(sg, condPartWorker, circuit.main, extIOMap, opt)
    w.writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
    if(opt.withVCD) { vcd.initializeOldValues(circuit) }
    if ((opt.trackParts || opt.trackSigs) && !opt.withVCD)
      w.writeLines(2, "cycle_count++;")
    if (opt.useCondParts)
      writeZoningBody(sg, condPartWorker, opt)
    else
      writeBodyInner(2, sg, opt)
    if(opt.withVCD) { vcd.compareOldValues(circuit) }
    if (containsAsserts) {
      w.writeLines(2, "if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
      w.writeLines(2, "if (!done_reset) assert_triggered = false;")
    }
    writeRegResetOverrides(sg)
    w.writeLines(0, "")
    if(opt.withVCD) { vcd.assignOldValues(circuit) }
    w.writeLines(2, "")
    w.writeLines(1, "}")
    // if (opt.trackParts || opt.trackSigs) {
    //   w.writeLines(1, s"~$topName() {")
    //   w.writeLines(2, "writeActToJson();")
    //   w.writeLines(1, "}")
    // }
    w.writeLines(0, "")
    if(opt.withVCD) { vcd.genWaveHeader() }
    w.writeLines(0, "")
    w.writeLines(0, s"} $topName;") //closing top module dec
    w.writeLines(0, "")
    w.writeLines(0, s"#endif  // $headerGuardName")
  }
}


class EssentCompiler(opt: OptFlags) {
  val readyForEssent: Seq[TransformDependency] =
    firrtl.stage.Forms.LowFormOptimized ++
    Seq(
//      Dependency(essent.passes.LegacyInvalidNodesForConds),
      Dependency(essent.passes.ReplaceAsyncRegs),
      Dependency(essent.passes.NoClockConnects),
      Dependency(essent.passes.RegFromMem1),
      Dependency(essent.passes.FactorMemReads),
      Dependency(essent.passes.FactorMemWrites),
      Dependency(essent.passes.SplitRegUpdates),
      Dependency(essent.passes.FixMulResultWidth),
      Dependency(essent.passes.DistinctTypeInstNames),
      Dependency(essent.passes.RemoveAsAsyncReset),
      Dependency(essent.passes.ReplaceRsvdKeywords)
    )

  def compileAndEmit(circuit: Circuit) {
    val topName = circuit.main
    if (opt.writeHarness) {
      val harnessFilename = new File(opt.outputDir, s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      if (opt.withVCD) { HarnessGenerator.topFile(topName, harnessWriter," |  dut.genWaveHeader();") }
      else { HarnessGenerator.topFile(topName, harnessWriter, "")}
      harnessWriter.close()
    }
    val firrtlCompiler = new transforms.Compiler(readyForEssent)
    val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
    if (opt.dumpLoFirrtl) {
      val debugWriter = new FileWriter(new File(opt.outputDir, s"$topName.lo.fir"))
      debugWriter.write(resultState.circuit.serialize)
      debugWriter.close()
    }
    val dutWriter = new FileWriter(new File(opt.outputDir, s"$topName.h"))
    val emitter = new EssentEmitter(opt, dutWriter)
    emitter.execute(resultState.circuit)
    dutWriter.close()
  }
}
