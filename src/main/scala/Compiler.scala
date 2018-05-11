package essent

import collection.mutable.HashMap
import java.io.Writer

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._

import firrtl._
import firrtl.annotations._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.PrimOps._
import firrtl.Utils._


class EmitCpp(writer: Writer) {
  val tabs = "  "

  // Writing methods
  def writeLines(indentLevel: Int, lines: String) {
    writeLines(indentLevel, Seq(lines))
  }

  def writeLines(indentLevel: Int, lines: Seq[String]) {
    lines foreach { s => writer write tabs*indentLevel + s + "\n" }
  }

  def declareModule(m: Module, topName: String) {
    val registers = findRegisters(m.body)
    val memories = findMemory(m.body)
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
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, registerDecs)
    writeLines(1, memDecs)
    writeLines(1, m.ports flatMap emitPort(modName == topName))
    writeLines(1, moduleDecs)
    writeLines(0, "")
    writeLines(1, s"$modName() {")
    writeLines(2, initializeVals(modName == topName)(m, registers, memories))
    writeLines(1, "}")
    if (modName == topName) {
      writeLines(0, "")
      writeLines(1, "void eval(bool update_registers, bool verbose, bool done_reset);")
      // writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
    } else {
      writeLines(0, s"} $modName;")
    }
  }

  def declareExtModule(m: ExtModule) {
    val modName = m.name
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, m.ports flatMap emitPort(true))
    writeLines(0, s"} $modName;")
  }

  def writeBodyInner(indentLevel: Int, sg: StatementGraph, doNotDec: Set[String], opt: OptFlags, keepAvail: Seq[String] = Seq()) {
    // sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
    if (opt.muxShadows)
      sg.coarsenMuxShadows(keepAvail)
    // NOTE: keepAvail not needed because potentially dangerous statements won't be found bottom-up
    //   potentially dangerous statements have hidden side effects (regs, mem writes, prints, stops)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case ms: MuxShadowed => {
        if (!doNotDec.contains(ms.name))
          writeLines(indentLevel, s"${genCppType(ms.mux.tpe)} ${ms.name};")
        writeLines(indentLevel, s"if (${emitExpr(ms.mux.cond)}) {")
        writeBodyInner(indentLevel + 1, StatementGraph(ms.tShadow), doNotDec + ms.name, opt, keepAvail)
        writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(ms.fShadow), doNotDec + ms.name, opt, keepAvail)
        writeLines(indentLevel, "}")
      }
      case _ => writeLines(indentLevel, emitStmt(doNotDec)(stmt))
    }}
  }

  def regResetOverrides(allRegDefs: Seq[DefRegister]): Seq[String] = {
    val updatesWithResets = allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
    resetGroups.toSeq flatMap {
      case (resetName, regDefs) => {
        val body = regDefs map {
          r => s"$tabs${r.name} = ${emitExpr(r.init)};"
        }
        Seq(s"if ($resetName) {") ++ body ++ Seq("}")
      }
    }
  }

  def genFlagName(regName: String): String = s"ZONE_$regName".replace('.','$')

  def genZoneFuncName(zoneName: String): String = s"EVAL_$zoneName".replace('.','$')

  def genDepZoneTriggers(consumers: Seq[String], condition: String): Seq[String] = {
    consumers map { consumer => s"${genFlagName(consumer)} |= $condition;" }
  }

  def genAllTriggers(signalToConsumers: Map[String, Seq[String]], suffix: String,
                     localTarg: Boolean = false): Seq[String] = {
    signalToConsumers.toSeq flatMap { case (name, consumers) => {
      val localName = if (localTarg) name.replace('.','$') else name
      genDepZoneTriggers(consumers, s"$name != $localName$suffix")
    }}
  }

  def writeZoningPredecs(
      sg: StatementGraph,
      topName: String,
      extIOtypes: Map[String, Type],
      startingDoNotDec: Set[String],
      opt: OptFlags) {
    val zoneNames = sg.getZoneNames()
    if (opt.trackAct) {
      writeLines(1, decZoneActTrackers(zoneNames))
      writeLines(1, "uint64_t cycle_count = 0;")
      val zoneNamesAndSizes = sg.stmtsOrdered flatMap { _ match {
        case az: ActivityZone => Some((az.name, az.memberStmts.size))
        case _ => None
      }}
      writeLines(1, "void printZoneActivities() {")
      writeLines(2, """fprintf(stderr, "%llu\n", cycle_count);""")
      writeLines(2, zoneActOutput(zoneNamesAndSizes))
      writeLines(2, zoneEffActSummary(zoneNamesAndSizes))
      writeLines(1, "}")
      writeLines(1, s"~$topName() {")
      writeLines(2, "printZoneActivities();")
      writeLines(1, "}")
    }
    // predeclare zone outputs
    val outputPairs = sg.getZoneOutputTypes()
    val outputConsumers = sg.getZoneInputMap()
    writeLines(0, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} $name;"})
    println(s"Output nodes: ${outputPairs.size}")
    val doNotDec = (outputPairs map { _._1 }).toSet ++ startingDoNotDec
    val nonMemCacheDecs = sg.getExternalZoneInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(1, nonMemCacheDecs)
    writeLines(1, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    // FUTURE: worry about namespace collisions with user variables
    writeLines(1, s"bool sim_cached = false;")
    writeLines(1, s"bool regs_set = false;")
    writeLines(1, s"bool update_registers;")
    writeLines(1, s"bool done_reset;")
    writeLines(1, s"bool verbose;")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(1, s"void ${genZoneFuncName(az.name)}() {")
        if (!az.name.contains("always"))
          writeLines(2, s"${genFlagName(az.name)} = false;")
        if (opt.trackAct)
          writeLines(2, s"${zoneActTrackerName(az.name)}++;")
        val cacheOldOutputs = az.outputTypes.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${name.replace('.','$')}$$old = $name;"
        }}
        writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](az.memberStmts)
        writeBodyInner(2, StatementGraph(noRegUpdates), doNotDec, opt, az.outputConsumers.keys.toSeq)
        // FUTURE: may be able to remove replace when $next is local
        val outputTriggers = az.outputTypes flatMap {
          case (name, tpe) => genDepZoneTriggers(az.outputConsumers(name), s"$name != ${name.replace('.','$')}$$old")
        }
        writeLines(2, outputTriggers.toSeq)
        // triggers for RegUpdates
        val regUpdateNamesInZone = regUpdates map findResultName
        val regOutputTriggers = regUpdateNamesInZone flatMap {
          name => genDepZoneTriggers(az.outputConsumers(name), s"$name != ${name.replace('.','$')}$$next")
        }
        writeLines(2, regOutputTriggers)
        writeLines(2, regUpdates flatMap emitStmt(doNotDec))
        // triggers for MemWrites
        val memWritesInZone = az.memberStmts collect { case mw: MemWrite => mw }
        val memWriteTriggerZones = memWritesInZone flatMap { mw => {
          val condition = s"${emitExpr(mw.wrEn)} && ${emitExpr(mw.wrMask)}"
          genDepZoneTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
        }}
        writeLines(2, memWriteTriggerZones)
        writeLines(1, "}")
      }
      case _ => throw new Exception("Statement at top-level is not a zone")
    }}
  }

  def writeZoningBody(sg: StatementGraph, doNotDec: Set[String], opt: OptFlags) {
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, "if (!sim_cached) {")
    writeLines(2, sg.getZoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
    writeLines(1, "}")
    writeLines(1, "sim_cached = regs_set;")
    writeLines(1, "this->update_registers = update_registers;")
    writeLines(1, "this->done_reset = done_reset;")
    writeLines(1, "this->verbose = verbose;")
    if (opt.trackAct)
      writeLines(1, "cycle_count++;")

    val outputConsumers = sg.getZoneInputMap()
    val externalZoneInputNames = sg.getExternalZoneInputNames()
    // do activity detection on other inputs (external IOs and resets)
    writeLines(1, genAllTriggers(selectFromMap(externalZoneInputNames, outputConsumers), "$old", true))
    // cache old versions
    val nonMemCaches = externalZoneInputNames map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)

    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        if (!az.name.contains("always")) {
          writeLines(1, s"if (${genFlagName(az.name)}) {")
          writeLines(2, s"${genZoneFuncName(az.name)}();")
          writeLines(1, "}")
        } else
        writeLines(1, s"${genZoneFuncName(az.name)}();")
      }
      case _ => writeLines(1, emitStmt(doNotDec)(stmt))
    }}

    writeLines(1, "regs_set = true;")
  }

  def zoneActTrackerName(zoneName: String) = s"ACT${zoneName.replace('.', '$')}"

  def decZoneActTrackers(zoneNames: Seq[String]) = {
    zoneNames map { zoneName => s"uint64_t ${zoneActTrackerName(zoneName)} = 0;"}
  }

  def zoneActOutput(zoneNamesAndSizes: Seq[(String,Int)]) = {
    zoneNamesAndSizes map {
      case (zoneName, zoneSize) => s"""fprintf(stderr, "$zoneName %llu %d\\n", ${zoneActTrackerName(zoneName)}, $zoneSize);"""
    }
  }

  def zoneEffActSummary(zoneNamesAndSizes: Seq[(String,Int)]) = {
    val sum = zoneNamesAndSizes map {
      case (zoneName, zoneSize) => s"total += ${zoneActTrackerName(zoneName)} * $zoneSize;"
    }
    val totalSize = (zoneNamesAndSizes map { _._2 }).sum
    val effAct = s"double eff_act = static_cast<double>(total) / $totalSize / cycle_count;"
    val printEffAct = """printf("Effective Activity: %g\n", eff_act);"""
    Seq("uint64_t total = 0;") ++ sum ++ Seq(effAct, printEffAct)
  }

  def writeEvalOuter(circuit: Circuit, opt: OptFlags) {
    val topName = circuit.main
    val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
    val allInstances = Seq((topModule.name, "")) ++
      findAllModuleInstances("", circuit)(topModule.body)
    val allBodies = allInstances flatMap {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => Some(flattenBodies(m, circuit, prefix))
        case em: ExtModule => None
      }
    }
    // FUTURE: handle top-level external inputs (other than reset)
    val extIOs = allInstances flatMap {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => None
        case em: ExtModule => em.ports map { port => (s"$prefix${port.name}", port.tpe) }
      }
    }
    val allRegDefs = allBodies flatMap findRegisters
    val regNames = allRegDefs map { _.name }
    val doNotDec = (regNames ++ (extIOs map { _._1 })).toSet
    val sg = StatementGraph(allBodies)
    if (opt.zoneAct)
      sg.coarsenIntoZones()
    else if (opt.regUpdates)
      sg.elideIntermediateRegUpdates()
    // FUTURE: worry about namespace collisions
    writeLines(1, "bool assert_triggered = false;")
    writeLines(1, "int assert_exit_code;")
    if (opt.zoneAct)
      writeZoningPredecs(sg, topName, extIOs.toMap, doNotDec, opt)
    writeLines(0, s"} $topName;") //closing module dec (was done to enable predecs for zones)
    writeLines(0, "")
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    if (opt.zoneAct)
      writeZoningBody(sg, doNotDec, opt)
    else
      writeBodyInner(1, sg, doNotDec, opt)
    writeLines(1, "if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
    if (regResetOverrides(allRegDefs).nonEmpty) {
      writeLines(1, "if (update_registers) {")
      // FUTURE: will overrides need triggers if zoned?
      writeLines(2, regResetOverrides(allRegDefs))
      writeLines(1, "}")
    }
    writeLines(0, "}")
    writeLines(0, "")
  }

  def emit(circuit: Circuit) {
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    writeLines(0, s"#ifndef $headerGuardName")
    writeLines(0, s"#define $headerGuardName")
    writeLines(0, "")
    writeLines(0, "#include <cstdint>")
    writeLines(0, "#include <cstdlib>")
    writeLines(0, "#include <uint.h>")
    writeLines(0, "#include <sint.h>")
    circuit.modules foreach {
      case m: Module => declareModule(m, topName)
      case m: ExtModule => declareExtModule(m)
    }
    val topModule = findModule(topName, circuit) match {case m: Module => m}
    writeLines(0, "")
    writeLines(0, "")
    // writeLines(0, s"void $topName::connect_harness(CommWrapper<struct $topName> *comm) {")
    // writeLines(1, HarnessGenerator.harnessConnections(topModule))
    // writeLines(0, "}")
    writeLines(0, "")
    // emitEvalTail(topName, circuit)
    writeEvalOuter(circuit, OptFlags(true, true, true, false))
    writeLines(0, s"#endif  // $headerGuardName")
  }
}

class CCEmitter(writer: Writer) extends firrtl.Emitter {
  def inputForm = LowForm
  def outputForm = LowForm

  def emit(state: CircuitState, lwriter: Writer): Unit = {
    val emitter = new essent.EmitCpp(lwriter)
    emitter.emit(state.circuit)
  }

  def execute(state: CircuitState): CircuitState = {
    val emitter = new essent.EmitCpp(writer)
    emitter.emit(state.circuit)
    state
  }
}

class FinalCleanups extends SeqTransform {
  def inputForm = MidForm
  def outputForm = LowForm
  val transforms = Seq(
    firrtl.passes.VerilogWrap,
    // essent.passes.InferAddw,
    // essent.passes.WireConstProp,
    // essent.passes.ZeroFromBits,
    // essent.passes.WireConstProp,
    // essent.passes.RandInitInvalids,
    essent.passes.NoClockConnects,
    essent.passes.RegFromMem1,
    essent.passes.FactorMemReads,
    essent.passes.FactorMemWrites,
    essent.passes.SplitRegUpdates,
    essent.passes.FixMulResultWidth)
    // passes.VerilogRename,
    // passes.VerilogPrep)
}

// FUTURE: use functionality within newer firrtl
class DumpLowFIRRTL(loFirWriter: Option[Writer]) extends Transform {
  def inputForm = MidForm
  def outputForm = LowForm
  def execute(state: CircuitState): CircuitState = {
    loFirWriter foreach { _.write(state.circuit.serialize) }
    state
  }
}

class CCCompiler(writer: Writer, loFirWriter: Option[Writer]) extends Compiler {
  def emitter = new CCEmitter(writer)
  def transforms: Seq[Transform] = Seq(
    new firrtl.ChirrtlToHighFirrtl,
    new firrtl.IRToWorkingIR,
    new firrtl.ResolveAndCheck,
    new firrtl.HighFirrtlToMiddleFirrtl,
    new firrtl.passes.memlib.InferReadWrite,
    new firrtl.passes.memlib.ReplSeqMem,
    new firrtl.MiddleFirrtlToLowFirrtl,
    // new firrtl.passes.InlineInstances,
    new firrtl.LowFirrtlOptimization,
    new FinalCleanups,
    new DumpLowFIRRTL(loFirWriter)
  )
}
