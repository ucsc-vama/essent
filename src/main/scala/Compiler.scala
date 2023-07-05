package essent

import java.io.{File, FileWriter, Writer}
import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import essent.DedupWorker._
import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency
import firrtl.stage.transforms
import firrtl.transforms.DedupedResult
import _root_.logger._

import scala.collection.mutable


class EssentEmitter(initialOpt: OptFlags, w: Writer, circuit: Circuit) extends LazyLogging {
  val flagVarName = "PARTflags"
  implicit val rn = new Renamer
  val actTrac = new ActivityTracker(w, initialOpt)
  val vcd = if (initialOpt.withVCD) Some(new Vcd(circuit,initialOpt,w,rn)) else None
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
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          w.writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        w.writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), opt)
        w.writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), opt)
        w.writeLines(indentLevel, "}")
      }
      case _ => {
        w.writeLines(indentLevel, emitStmt(stmt))
        if (opt.withVCD)  vcd.get.compSmallEval(stmt, indentLevel)
        if (opt.trackSigs) actTrac.emitSigTracker(stmt, indentLevel)
      }
    }}
  }

  def checkRegResetSafety(sg: StatementGraph) {
    val updatesWithResets = sg.allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    assert(updatesWithResets.isEmpty)
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
          w.writeLines(2, s"${actTrac.actVarName}[${cp.id}]++;")

        val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
        w.writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
        val bodySG = StatementGraph(noRegUpdates)
        if (opt.conditionalMuxes)
          MakeCondMux(bodySG, rn, keepAvail)
        writeBodyInner(2, bodySG, opt, keepAvail)
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


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute(circuit: Circuit, annotations: AnnotationSeq) {
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
    }

    if(opt.withVCD) {
      w.writeLines(0, "uint64_t vcd_cycle_count = 0;")
      w.writeLines(1,s"""FILE *outfile;""")
    }
    val sg = StatementGraph(circuit, opt.removeFlatConnects)
    logger.info(sg.makeStatsString)
    val containsAsserts = sg.containsStmtOfType[Stop]()
    val extIOMap = findExternalPorts(circuit)
    val condPartWorker = MakeCondPart(sg, rn, extIOMap)
    rn.populateFromSG(sg, extIOMap)


    if (opt.useCondParts) {
      assert(opt.dedup)
      // Dedup + VCD not supported yet
      assert(!opt.withVCD)

      // Start timer
      val startTime = System.currentTimeMillis()

      // Parse module and instance information
      val modInstInfo = new ModuleInstanceInfo(circuit, annotations, sg)

      // Determine which mod/insts to dedup
      // Note: Currently only dedup 1 mod
      // 1. Find out num of instances of each module
      val modInstanceCount = modInstInfo.internalModInstanceTable.map{ case (modName, insts) => modName -> insts.size}
      // 2. Find out reduction of [#IR nodes] as dedup benefits
      val modDedupBenefits = modInstanceCount.map{ case(modName, nInst) => modName -> ((nInst - 1) * modInstInfo.internalModIRSize(modName))}
      // 3. Sort
      val modDedupBenefitsSorted = modDedupBenefits.toSeq.sortBy(_._2)(Ordering[Int].reverse)

      // Report benefits
      logger.info("=" * 50)
      logger.info("Module Name, Num of Instances, Dedup Benefits")
      for (i <- 0 to Seq(5, modDedupBenefitsSorted.size).min) {
        val modName = modDedupBenefitsSorted(i)._1
        val modDedupBenefit = modDedupBenefitsSorted(i)._2
        logger.info(s"${modName}, ${modInstanceCount(modName)}, ${modDedupBenefit}")
      }
      logger.info("=" * 50)

      // Choose which module to deduplicate (most benefit)
      val dedupMod = modDedupBenefitsSorted.head._1
      val dedupInstances = modInstInfo.allModInstanceTable(dedupMod)

      val dedupBenefit = modDedupBenefitsSorted.head._2
      val originalIRSize = modInstInfo.instInclusiveNodesTable("").size // Root instance is always named as ""
      logger.info(s"Deduplicate module [${dedupMod}], benefit (num IR nodes) ${dedupBenefit} (-${dedupBenefit.toFloat * 100 / originalIRSize}%)")
      logger.info(s"Original design has ${originalIRSize} IR nodes")
      logger.info(s"Dedup instances: ${dedupInstances}")


      val stopTime = System.currentTimeMillis()
      logger.info(s"Took ${stopTime - startTime} ms to find proper dedup module")



      if (dedupInstances.size <= 1) {
        println("Input circuit contains no duplicated modules!")
        condPartWorker.doOpt((opt.partCutoff))
      } else {
        condPartWorker.doOptForDedup(opt.partCutoff, dedupInstances, modInstInfo)

      }

    } else {
      if (opt.regUpdates)
        OptElideRegUpdates(sg)
      if (opt.conditionalMuxes)
        MakeCondMux(sg, rn, Set())
    }
    checkRegResetSafety(sg)
    if (opt.trackParts || opt.trackSigs || opt.trackExts)
      actTrac.declareTop(sg, topName, condPartWorker)

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
    if (opt.withVCD)  { vcd.get.declareOldvaluesAll(circuit) }
    if(opt.withVCD) { vcd.get.genWaveHeader() }
    if (containsAsserts) {
      w.writeLines(1, "bool assert_triggered = false;")
      w.writeLines(1, "int assert_exit_code;")
      w.writeLines(0, "")
    }
    if (opt.useCondParts)
      writeZoningPredecs(sg, condPartWorker, circuit.main, extIOMap, opt)
    w.writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
    if(opt.withVCD) { vcd.get.initializeOldValues(circuit) }
    if (opt.trackParts || opt.trackSigs)
      w.writeLines(2, "act_cycle_count++;")
    if (opt.useCondParts)
      writeZoningBody(sg, condPartWorker, opt)
    else
      writeBodyInner(2, sg, opt)
    if(opt.withVCD) { vcd.get.compareOldValues(circuit) }
    if (containsAsserts) {
      w.writeLines(2, "if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
      w.writeLines(2, "if (!done_reset) assert_triggered = false;")
    }
    w.writeLines(0, "")
    if(opt.withVCD) { vcd.get.assignOldValues(circuit) }
    w.writeLines(2, "")
    w.writeLines(1, "}")
    // if (opt.trackParts || opt.trackSigs) {
    //   w.writeLines(1, s"~$topName() {")
    //   w.writeLines(2, "writeActToJson();")
    //   w.writeLines(1, "}")
    // }
    w.writeLines(0, "")
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
    val emitter = new EssentEmitter(opt, dutWriter,resultState.circuit)
    emitter.execute(resultState.circuit, resultState.annotations)
    dutWriter.close()
  }
}
