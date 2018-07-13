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


class CppEmitter(initialOpt: OptFlags, writer: Writer) extends firrtl.Emitter {
  def inputForm = LowForm
  def outputForm = LowForm

  val tabs = "  "
  val flagVarName = "ZONEflags"
  val actVarName = "ACTcounts"

  // Writing To File
  //----------------------------------------------------------------------------
  def writeLines(indentLevel: Int, lines: String) {
    writeLines(indentLevel, Seq(lines))
  }

  def writeLines(indentLevel: Int, lines: Seq[String]) {
    lines foreach { s => writer write tabs*indentLevel + s + "\n" }
  }


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


  // Write General-purpose Eval
  //----------------------------------------------------------------------------
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

  def writeRegResetOverrides(sg: StatementGraph) {
    val updatesWithResets = sg.allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
    val overridesToWrite = resetGroups.toSeq flatMap {
      case (resetName, regDefs) => {
        val body = regDefs map {
          r => s"$tabs${r.name} = ${emitExpr(r.init)};"
        }
        Seq(s"if ($resetName) {") ++ body ++ Seq("}")
      }
    }
    if (overridesToWrite.nonEmpty) {
      writeLines(2, "if (update_registers) {")
      // FUTURE: will overrides need triggers if zoned?
      writeLines(3, overridesToWrite)
      writeLines(2, "}")
    }
  }


  // Write Zoning Optimized Eval
  //----------------------------------------------------------------------------
  def genZoneFuncName(zoneID: Int): String = "EVAL_" + zoneID

  def genDepZoneTriggers(consumerIDs: Seq[Int], condition: String): Seq[String] = {
    consumerIDs map { consumerID => s"$flagVarName[$consumerID] |= $condition;" }
  }

  def genAllTriggers(signalNames: Seq[String], outputConsumers: Map[String, Seq[Int]],
      suffix: String): Seq[String] = {
    selectFromMap(signalNames, outputConsumers).toSeq flatMap { case (name, consumerIDs) => {
      val localName = name.replace('.','$')
      genDepZoneTriggers(consumerIDs, s"$name != $localName$suffix")
    }}
  }

  def writeZoningPredecs(
      sg: StatementGraph,
      topName: String,
      extIOtypes: Map[String, Type],
      startingDoNotDec: Set[String],
      opt: OptFlags) {
    val numZones = sg.getNumZones()
    if (opt.trackAct) {
      writeLines(1, s"std::array<uint64_t,$numZones> $actVarName{};")
      writeLines(1, "uint64_t cycle_count = 0;")
      val zoneIDsAndSizes = sg.stmtsOrdered flatMap { _ match {
        case az: ActivityZone => Some((az.id, az.memberStmts.size))
        case _ => None
      }}
      writeLines(1, "void printZoneActivities() {")
      writeLines(2, """fprintf(stderr, "%llu\n", cycle_count);""")
      writeLines(2, zoneActOutput(zoneIDsAndSizes))
      writeLines(2, zoneEffActSummary(zoneIDsAndSizes))
      writeLines(1, "}")
      writeLines(1, s"~$topName() {")
      writeLines(2, "printZoneActivities();")
      writeLines(1, "}")
    }
    // predeclare zone outputs
    val outputPairs = sg.getZoneOutputsToDeclare()
    val outputConsumers = sg.getZoneInputMap()
    writeLines(0, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} $name;"})
    println(s"Output nodes: ${outputPairs.size}")
    val doNotDec = (outputPairs map { _._1 }).toSet ++ startingDoNotDec
    val nonMemCacheDecs = sg.getExternalZoneInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(1, nonMemCacheDecs)
    writeLines(1, s"std::array<bool,$numZones> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    writeLines(1, s"bool sim_cached = false;")
    writeLines(1, s"bool regs_set = false;")
    writeLines(1, s"bool update_registers;")
    writeLines(1, s"bool done_reset;")
    writeLines(1, s"bool verbose;")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(1, s"void ${genZoneFuncName(az.id)}() {")
        if (!az.alwaysActive)
          writeLines(2, s"$flagVarName[${az.id}] = false;")
        if (opt.trackAct)
          writeLines(2, s"${zoneActTrackerName(az.id)}++;")
        val cacheOldOutputs = az.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${name.replace('.','$')}$$old = $name;"
        }}
        writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](az.memberStmts)
        writeBodyInner(2, StatementGraph(noRegUpdates), doNotDec, opt, outputConsumers.keys.toSeq)
        writeLines(2, genAllTriggers(az.outputsToDeclare.keys.toSeq, outputConsumers, "$old"))
        val regUpdateNamesInZone = regUpdates flatMap findResultName
        writeLines(2, genAllTriggers(regUpdateNamesInZone, outputConsumers, "$next"))
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
      case _ => throw new Exception(s"Statement at top-level is not a zone (${stmt.serialize})")
    }}
  }

  def writeZoningBody(sg: StatementGraph, doNotDec: Set[String], opt: OptFlags) {
    writeLines(2, "if (reset || !done_reset) {")
    writeLines(3, "sim_cached = false;")
    writeLines(3, "regs_set = false;")
    writeLines(2, "}")
    writeLines(2, "if (!sim_cached) {")
    writeLines(3, s"$flagVarName.fill(true);")
    writeLines(2, "}")
    writeLines(2, "sim_cached = regs_set;")
    writeLines(2, "this->update_registers = update_registers;")
    writeLines(2, "this->done_reset = done_reset;")
    writeLines(2, "this->verbose = verbose;")
    if (opt.trackAct)
      writeLines(2, "cycle_count++;")
    val outputConsumers = sg.getZoneInputMap()
    val externalZoneInputNames = sg.getExternalZoneInputNames()
    // do activity detection on other inputs (external IOs and resets)
    writeLines(2, genAllTriggers(externalZoneInputNames, outputConsumers, "$old"))
    // cache old versions
    val nonMemCaches = externalZoneInputNames map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(2, nonMemCaches.toSeq)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        if (!az.alwaysActive)
          writeLines(2, s"if ($flagVarName[${az.id}]) ${genZoneFuncName(az.id)}();")
        else
          writeLines(2, s"${genZoneFuncName(az.id)}();")
      }
      case _ => writeLines(2, emitStmt(doNotDec)(stmt))
    }}

    writeLines(2, "regs_set = true;")
  }

  def zoneActTrackerName(zoneID: Int) = s"$actVarName[$zoneID]"

  def zoneActOutput(zoneIDsAndSizes: Seq[(Int,Int)]) = {
    zoneIDsAndSizes map {
      case (zoneID, zoneSize) => s"""fprintf(stderr, "$zoneID %llu $zoneSize\\n", ${zoneActTrackerName(zoneID)});"""
    }
  }

  def zoneEffActSummary(zoneIDsAndSizes: Seq[(Int,Int)]) = {
    val sum = zoneIDsAndSizes map {
      case (zoneID, zoneSize) => s"total += ${zoneActTrackerName(zoneID)} * $zoneSize;"
    }
    val totalSize = (zoneIDsAndSizes map { _._2 }).sum
    val effAct = s"double eff_act = static_cast<double>(total) / $totalSize / cycle_count;"
    val printEffAct = """printf("Effective Activity: %g\n", eff_act);"""
    Seq("uint64_t total = 0;") ++ sum ++ Seq(effAct, printEffAct)
  }


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def emit(state: firrtl.CircuitState, writer: java.io.Writer) {}
  // TODO: unimplemented, but also deprecated in firrtl

  def execute(state: CircuitState): CircuitState = {
    val opt = initialOpt
    val circuit = state.circuit
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    writeLines(0, s"#ifndef $headerGuardName")
    writeLines(0, s"#define $headerGuardName")
    writeLines(0, "")
    writeLines(0, "#include <array>")
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
    // writeLines(0, "")
    // writeLines(0, s"void $topName::connect_harness(CommWrapper<struct $topName> *comm) {")
    // writeLines(1, HarnessGenerator.harnessConnections(topModule))
    // writeLines(0, "}")
    writeLines(0, "")
    val sg = StatementGraph(circuit)
    val extIOMap = findExternalPorts(circuit)
    val doNotDec = sg.stateElemNames.toSet ++ extIOMap.keySet
    if (opt.zoneAct)
      sg.coarsenIntoZones()
    else if (opt.regUpdates)
      sg.elideIntermediateRegUpdates()
    writeLines(1, "bool assert_triggered = false;")
    writeLines(1, "int assert_exit_code;")
    if (opt.zoneAct)
      writeZoningPredecs(sg, circuit.main, extIOMap, doNotDec, opt)
    writeLines(0, "")
    writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
    if (opt.zoneAct)
      writeZoningBody(sg, doNotDec, opt)
    else
      writeBodyInner(2, sg, doNotDec, opt)
    writeLines(2, "if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
    writeRegResetOverrides(sg)
    writeLines(1, "}")
    writeLines(0, s"} $topName;") //closing top module dec
    writeLines(0, "")
    writeLines(0, s"#endif  // $headerGuardName")
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
    essent.passes.ReplaceAsyncRegs,
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

class CCCompiler(opt: OptFlags, writer: Writer, loFirWriter: Option[Writer]) extends Compiler {
  def emitter = new CppEmitter(opt, writer)
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
