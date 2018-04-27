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
      Seq(s"$typeStr $regName;", s"$typeStr $regName$$next;")
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

  def writeBodyInner(indentLevel: Int, sg: StatementGraph, doNotDec: Set[String], optMuxes: Boolean, doNotShadow: Seq[String]=Seq()) {
    // TODO: trust others to perform opts to merge regs or mems
    // sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
    if (optMuxes)
      sg.coarsenMuxShadows(doNotShadow)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case ms: MuxShadowed => {
        if (!doNotDec.contains(ms.name))
          writeLines(indentLevel, s"${genCppType(ms.mux.tpe)} ${ms.name};")
        writeLines(indentLevel, s"if (${emitExpr(ms.mux.cond)}) {")
        writeBodyInner(indentLevel + 1, StatementGraph(ms.tShadow), doNotDec + ms.name, optMuxes, doNotShadow)
        writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(ms.fShadow), doNotDec + ms.name, optMuxes, doNotShadow)
        writeLines(indentLevel, "}")
      }
      case _ => writeLines(indentLevel, emitStmt(doNotDec)(stmt))
    }}
  }

  def writeBodyUnoptSG(indentLevel: Int, bodies: Seq[Statement], doNotDec: Set[String] = Set()) {
    val sg = StatementGraph(bodies)
    sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
  }

  def writeBodyRegTailOptSG(indentLevel: Int, bodies: Seq[Statement], doNotDec: Set[String], regNames: Seq[String]): Seq[String] = {
    val sg = StatementGraph(bodies)
    val mergedRegs = sg.mergeRegsSafe(regNames)
    sg.updateMergedRegWrites(mergedRegs)
    sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
    mergedRegs
  }

  def writeBodyMergeMWSG(indentLevel: Int, bodies: Seq[Statement], doNotDec: Set[String],
                         regNames: Seq[String], memWrites: Seq[MemWrite]): Seq[String] = {
    val sg = StatementGraph(bodies)
    sg.mergeMemWritesIntoSG(memWrites)
    val mergedRegs = sg.mergeRegsSafe(regNames)
    sg.updateMergedRegWrites(mergedRegs)
    sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
    mergedRegs
  }

  def writeBodyMuxOptSG(indentLevel: Int, bodies: Seq[Statement], doNotShadow: Seq[String],
      doNotDec: Set[String], regsToConsider: Seq[String]=Seq()): Seq[String] = {
    if (bodies.nonEmpty) {
      val sg = StatementGraph(bodies)
      sg.coarsenMuxShadows(doNotShadow)
      val mergedRegs = sg.mergeRegsSafe(regsToConsider)
      sg.updateMergedRegWrites(mergedRegs)
      sg.stmtsOrdered foreach { stmt => stmt match {
        case ms: MuxShadowed => {
          if (!doNotDec.contains(ms.name))
            writeLines(indentLevel, s"${genCppType(ms.mux.tpe)} ${ms.name};")
          writeLines(indentLevel, s"if (${emitExpr(ms.mux.cond)}) {")
          writeBodyMuxOptSG(indentLevel + 1, ms.tShadow, doNotShadow, doNotDec + ms.name)
          writeLines(indentLevel, "} else {")
          writeBodyMuxOptSG(indentLevel + 1, ms.fShadow, doNotShadow, doNotDec + ms.name)
          writeLines(indentLevel, "}")
        }
        case _ => writeLines(indentLevel, emitStmt(doNotDec)(stmt))
      }}
      mergedRegs
    } else Seq()
  }

  def writeBodyMuxOptMemSG(indentLevel: Int, bodies: Seq[Statement], doNotShadow: Seq[String],
      doNotDec: Set[String], regsToConsider: Seq[String]=Seq(), memWrites: Seq[MemWrite]): Seq[String] = {
    if (bodies.nonEmpty) {
      val sg = StatementGraph(bodies)
      sg.mergeMemWritesIntoSG(memWrites)
      sg.coarsenMuxShadows(doNotShadow)
      val mergedRegs = sg.mergeRegsSafe(regsToConsider)
      sg.updateMergedRegWrites(mergedRegs)
      sg.stmtsOrdered foreach { stmt => stmt match {
        case ms: MuxShadowed => {
          if (!doNotDec.contains(ms.name))
            writeLines(indentLevel, s"${genCppType(ms.mux.tpe)} ${ms.name};")
          writeLines(indentLevel, s"if (${emitExpr(ms.mux.cond)}) {")
          writeBodyMuxOptSG(indentLevel + 1, ms.tShadow, doNotShadow, doNotDec + ms.name)
          writeLines(indentLevel, "} else {")
          writeBodyMuxOptSG(indentLevel + 1, ms.fShadow, doNotShadow, doNotDec + ms.name)
          writeLines(indentLevel, "}")
        }
        case _ => writeLines(indentLevel, emitStmt(doNotDec)(stmt))
      }}
      mergedRegs
    } else Seq()
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

  def writeBodyZoneOptSG(
      bodies: Seq[Statement],
      topName: String,
      memWrites: Seq[MemWrite],
      extIOtypes: Map[String, Type],
      regNames: Seq[String],
      keepAvail: Seq[String],
      startingDoNotDec: Set[String],
      regsToConsider: Seq[String]): Seq[String] = {
    val trackActivity = true
    val sg = StatementGraph(bodies)
    // val mergedRegs = sg.mergeRegsSafe(regsToConsider)
    sg.coarsenIntoZones(keepAvail)
    val mergedRegs = sg.mergeRegUpdatesIntoZones(regsToConsider)
    val mergedRegsSet = (mergedRegs map { _ + "$next"}).toSet
    // predeclare zone eval funcs
    val zoneEvalFuncPredDecs = sg.getZoneNames() map {
      zoneName => s"void ${genZoneFuncName(zoneName)}(bool update_registers);"
    }
    writeLines(1, zoneEvalFuncPredDecs)
    writeLines(0, s"} $topName;")
    // predeclare zone outputs
    val outputPairs = sg.getZoneOutputTypes()
    val outputConsumers = sg.getZoneInputMap()
    writeLines(0, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} $name;"})
    println(s"Output nodes: ${outputPairs.size}")
    val doNotDec = (outputPairs map { _._1 }).toSet ++ startingDoNotDec
    val otherInputs = sg.getExternalZoneInputs() diff regNames
    val memNames = (memWrites map { _.memName }).toSet
    val (memInputs, nonMemInputs) = otherInputs partition { memNames.contains(_) }
    val nonMemCacheTypes = nonMemInputs.toSeq map {
      name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
    }
    val nonMemCacheDecs = (nonMemCacheTypes zip nonMemInputs.toSeq) map {
      case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(0, nonMemCacheDecs)
    val zoneNames = sg.getZoneNames()
    writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    writeLines(0, s"bool sim_cached = false;")
    writeLines(0, s"bool regs_set = false;")
    writeLines(0, "bool assert_triggered = false;")
    writeLines(0, "int assert_exit_code;")

    // emit zones
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(0, s"void $topName::${genZoneFuncName(az.name)}(bool update_registers) {")
        writeLines(1, s"${genFlagName(az.name)} = false;")
        val cacheOldOutputs = az.outputTypes.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} $name$$old = $name;"
        }}
        writeLines(1, cacheOldOutputs)
        writeBodyMuxOptSG(1, az.memberStmts, keepAvail ++ doNotDec, doNotDec)
        // writeBodyUnoptSG(2, az.memberStmts, doNotDec ++ regNames)
        val outputTriggers = az.outputConsumers.toSeq flatMap {
          case (name, consumers) => genDepZoneTriggers(consumers, s"$name != $name$$old")
        }
        writeLines(1, outputTriggers)
        val mergedRegsInZone = az.memberNames filter mergedRegsSet map { _.replaceAllLiterally("$next","") }
        writeLines(1, genAllTriggers(selectFromMap(mergedRegsInZone, outputConsumers), "$next"))
        writeLines(1, mergedRegsInZone map { regName => s"if (update_registers) $regName = $regName$$next;" })
        // NOTE: not using RegUpdate since want to do reg change detection
        writeLines(0, "}")
      }
      case _ => throw new Exception("Statement at top-level is not a zone")
    }}

    if (trackActivity) {
      writeLines(0, decZoneActTrackers(zoneNames))
      val zoneNamesAndSizes = sg.stmtsOrdered flatMap { _ match {
        case az: ActivityZone => Some((az.name, az.memberStmts.size))
        case _ => None
      }}
      writeLines(0, "void printZoneActivities() {")
      writeLines(1, zoneActOutput(zoneNamesAndSizes))
      writeLines(0, "}")
    }

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, "if (!sim_cached) {")
    writeLines(2, zoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
    writeLines(1, "}")
    writeLines(1, "sim_cached = regs_set;")

    // do activity detection on other inputs (external IOs and resets)
    writeLines(1, genAllTriggers(selectFromMap(nonMemInputs, outputConsumers), "$old", true))
    // cache old versions
    val nonMemCaches = nonMemInputs map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)

    // emit zone launches and unzoned statements
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(1, s"if (${genFlagName(az.name)}) {")
        writeLines(2, s"${genZoneFuncName(az.name)}(update_registers);")
        writeLines(1, "}")
      }
      case _ => writeLines(1, emitStmt(doNotDec)(stmt))
    }}
    // trigger zones based on mem writes
    // NOTE: if mem has multiple write ports, either can trigger wakeups
    val memEnablesAndMasks = (memWrites map {
      mw => (mw.memName, Seq(emitExpr(mw.wrEn), emitExpr(mw.wrMask)))
    }).toMap
    val memWriteTriggerZones = memInputs.toSeq flatMap { flagName => {
      val condition = memEnablesAndMasks(flagName).mkString(" && ")
      genDepZoneTriggers(outputConsumers(flagName), condition)
    }}
    writeLines(1, memWriteTriggerZones)
    // trigger zone based on reg changes
    writeLines(1, genAllTriggers(selectFromMap(regNames diff mergedRegs, outputConsumers), "$next"))
    mergedRegs
  }

  def writeZoningPredecs(
      sg: StatementGraph,
      topName: String,
      memWrites: Seq[MemWrite],
      extIOtypes: Map[String, Type],
      regNames: Seq[String],
      mergedRegs: Seq[String],
      startingDoNotDec: Set[String],
      keepAvail: Seq[String]) {
    val zoneEvalFuncPredDecs = sg.getZoneNames() map {
      zoneName => s"void ${genZoneFuncName(zoneName)}(bool update_registers);"
    }
    writeLines(1, zoneEvalFuncPredDecs)
    writeLines(0, s"} $topName;")
    // predeclare zone outputs
    val outputPairs = sg.getZoneOutputTypes()
    val outputConsumers = sg.getZoneInputMap()
    writeLines(0, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} $name;"})
    println(s"Output nodes: ${outputPairs.size}")
    val mergedRegsSet = (mergedRegs map { _ + "$next"}).toSet
    val doNotDec = (outputPairs map { _._1 }).toSet ++ startingDoNotDec
    val otherInputs = sg.getExternalZoneInputs() diff regNames
    val memNames = (memWrites map { _.memName }).toSet
    val (memInputs, nonMemInputs) = otherInputs partition { memNames.contains(_) }
    val nonMemCacheTypes = nonMemInputs.toSeq map {
      name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
    }
    val nonMemCacheDecs = (nonMemCacheTypes zip nonMemInputs.toSeq) map {
      case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(0, nonMemCacheDecs)
    val zoneNames = sg.getZoneNames()
    writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    writeLines(0, s"bool sim_cached = false;")
    writeLines(0, s"bool regs_set = false;")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(0, s"void $topName::${genZoneFuncName(az.name)}(bool update_registers) {")
        writeLines(1, s"${genFlagName(az.name)} = false;")
        val cacheOldOutputs = az.outputTypes.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} $name$$old = $name;"
        }}
        writeLines(1, cacheOldOutputs)
        writeBodyInner(1, StatementGraph(az.memberStmts), doNotDec, true, keepAvail ++ doNotDec)
        // writeBodyMuxOptSG(1, az.memberStmts, keepAvail ++ doNotDec, doNotDec)
        // writeBodyUnoptSG(2, az.memberStmts, doNotDec ++ regNames)
        val outputTriggers = az.outputConsumers.toSeq flatMap {
          case (name, consumers) => genDepZoneTriggers(consumers, s"$name != $name$$old")
        }
        writeLines(1, outputTriggers)
        val mergedRegsInZone = az.memberNames filter mergedRegsSet map { _.replaceAllLiterally("$next","") }
        writeLines(1, genAllTriggers(selectFromMap(mergedRegsInZone, outputConsumers), "$next"))
        writeLines(1, mergedRegsInZone map { regName => s"if (update_registers) $regName = $regName$$next;" })
        // NOTE: not using RegUpdate since want to do reg change detection
        // trigger zones based on mem writes
        val memWritesInZone = az.memberStmts flatMap findInstancesOf[MemWrite]
        val memWriteTriggerZones = memWritesInZone flatMap { mw => {
          val condition = s"${emitExpr(mw.wrEn)} && ${emitExpr(mw.wrMask)}"
          genDepZoneTriggers(outputConsumers(mw.memName), condition)
        }}
        writeLines(1, memWriteTriggerZones)
        writeLines(0, "}")
      }
      case _ => throw new Exception("Statement at top-level is not a zone")
    }}
  }

  def writeZoningBody(sg: StatementGraph, regNames: Seq[String], unmergedRegs: Seq[String],
                      memWrites: Seq[MemWrite], doNotDec: Set[String]) {
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, "if (!sim_cached) {")
    writeLines(2, sg.getZoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
    writeLines(1, "}")
    writeLines(1, "sim_cached = regs_set;")

    val outputConsumers = sg.getZoneInputMap()
    val memNames = memWrites map { _.memName }
    val nonMemInputs = sg.getExternalZoneInputs() diff (regNames ++ memNames)
    // do activity detection on other inputs (external IOs and resets)
    writeLines(1, genAllTriggers(selectFromMap(nonMemInputs, outputConsumers), "$old", true))
    // cache old versions
    val nonMemCaches = nonMemInputs map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)

    // emit zone launches and unzoned statements
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(1, s"if (${genFlagName(az.name)}) {")
        writeLines(2, s"${genZoneFuncName(az.name)}(update_registers);")
        writeLines(1, "}")
      }
      case _ => writeLines(1, emitStmt(doNotDec)(stmt))
    }}
    // trigger zones based on mem writes
    // NOTE: if mem has multiple write ports, either can trigger wakeups
    // val memWriteTriggerZones = memWrites flatMap { mw => {
    //   val condition = s"${emitExpr(mw.wrEn)} && ${emitExpr(mw.wrMask)}"
    //   genDepZoneTriggers(outputConsumers(mw.memName), condition)
    // }}
    // writeLines(1, memWriteTriggerZones)
    // trigger zone based on reg changes
    writeLines(1, genAllTriggers(selectFromMap(unmergedRegs, outputConsumers), "$next"))
  }

  def writeBodyZoneOptSGMem(
      bodies: Seq[Statement],
      topName: String,
      memWrites: Seq[MemWrite],
      extIOtypes: Map[String, Type],
      regNames: Seq[String],
      keepAvail: Seq[String],
      startingDoNotDec: Set[String],
      regsToConsider: Seq[String]): Seq[String] = {
    val trackActivity = true
    val sg = StatementGraph(bodies)
    sg.mergeMemWritesIntoSG(memWrites)
    // val mergedRegs = sg.mergeRegsSafe(regsToConsider)
    val memNames = (memWrites map { _.memName }).toSet
    sg.coarsenIntoZones(keepAvail filter { !memNames.contains(_)})
    // val mergedRegs = Seq[String]()
    val mergedRegs = sg.mergeRegUpdatesIntoZones(regsToConsider)
    val mergedRegsSet = (mergedRegs map { _ + "$next"}).toSet
    // predeclare zone outputs
    val outputPairs = sg.getZoneOutputTypes()
    val outputConsumers = sg.getZoneInputMap()
    writeLines(0, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} $name;"})
    println(s"Output nodes: ${outputPairs.size}")
    val doNotDec = (outputPairs map { _._1 }).toSet ++ startingDoNotDec
    val otherInputs = sg.getExternalZoneInputs() diff regNames
    val (memInputs, nonMemInputs) = otherInputs partition { memNames.contains(_) }
    val nonMemCacheTypes = nonMemInputs.toSeq map {
      name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
    }
    val nonMemCacheDecs = (nonMemCacheTypes zip nonMemInputs.toSeq) map {
      case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(0, nonMemCacheDecs)
    val zoneNames = sg.getZoneNames()
    writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    writeLines(0, s"bool sim_cached = false;")
    writeLines(0, s"bool regs_set = false;")

    if (trackActivity) {
      writeLines(0, decZoneActTrackers(zoneNames))
      val zoneNamesAndSizes = sg.stmtsOrdered flatMap { _ match {
        case az: ActivityZone => Some((az.name, az.memberStmts.size))
        case _ => None
      }}
      writeLines(0, "void printZoneActivities() {")
      writeLines(1, zoneActOutput(zoneNamesAndSizes))
      writeLines(0, "}")
    }

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, "bool assert_triggered = false;")
    writeLines(1, "int assert_exit_code;")
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, "if (!sim_cached) {")
    writeLines(2, zoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
    writeLines(1, "}")
    writeLines(1, "sim_cached = regs_set;")

    // do activity detection on other inputs (external IOs and resets)
    val nonMemChangeDetects = nonMemInputs flatMap { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      genDepZoneTriggers(outputConsumers(sigName), s"$sigName != $oldVersion")
    }}
    writeLines(1, nonMemChangeDetects.toSeq)
    // cache old versions
    val nonMemCaches = nonMemInputs map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)

    // emit zones (and unzoned statements)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case az: ActivityZone => {
        writeLines(1, s"if (${genFlagName(az.name)}) {")
        writeLines(2, s"${genFlagName(az.name)} = false;")
        if (trackActivity)
          writeLines(2, s"${zoneActTrackerName(az.name)}++;")
        val cacheOldOutputs = az.outputTypes.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} $name$$old = $name;"
        }}
        writeLines(2, cacheOldOutputs)
        writeBodyMuxOptSG(2, az.memberStmts, keepAvail ++ doNotDec, doNotDec)
        // writeBodyUnoptSG(2, az.memberStmts, doNotDec ++ regNames)
        val outputTriggers = az.outputConsumers.toSeq flatMap {
          case (name, consumers) => genDepZoneTriggers(consumers, s"$name != $name$$old")
        }
        writeLines(2, outputTriggers)
        val mergedRegsInZone = az.memberNames filter mergedRegsSet map { _.replaceAllLiterally("$next","") }
        val regsTriggerZones = mergedRegsInZone flatMap {
          regName => genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
        }
        writeLines(2, regsTriggerZones)
        writeLines(2, mergedRegsInZone map { regName => s"if (update_registers) $regName = $regName$$next;" })
        // NOTE: not using RegUpdate since want to do reg change detection
        val memWritesInZone = az.memberStmts flatMap findInstancesOf[MemWrite]
        val memsWrittenInZone = (memWritesInZone map { _.memName }).distinct
        // trigger zones based on mem writes
        // NOTE: if mem has multiple write ports, either can trigger wakeups
        val memEnablesAndMasks = (memWritesInZone map {
          mw => (mw.memName, Seq(emitExpr(mw.wrEn), emitExpr(mw.wrMask)))
        }).toMap
        val memWriteTriggerZones = memsWrittenInZone flatMap { flagName => {
          val condition = memEnablesAndMasks(flagName).mkString(" && ")
          genDepZoneTriggers(outputConsumers(flagName), condition)
        }}
        writeLines(2, memWriteTriggerZones)
        writeLines(1, "}")
      }
      case _ => writeLines(1, emitStmt(doNotDec)(stmt))
    }}
    // trigger zone based on reg changes
    val regsTriggerZones = (regNames diff mergedRegs) flatMap { regName => {
      if (outputConsumers.contains(regName))
        genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
      else Seq()
    }}
    writeLines(1, regsTriggerZones)
    mergedRegs
  }

  def zoneActTrackerName(zoneName: String) = s"ACT${zoneName.replace('.', '$')}"

  def decZoneActTrackers(zoneNames: Seq[String]) = {
    zoneNames map { zoneName => s"uint64_t ${zoneActTrackerName(zoneName)} = 0;"}
  }

  def zoneActOutput(zoneNamesAndSizes: Seq[(String,Int)]) = {
    zoneNamesAndSizes map {
      case (zoneName, zoneSize) => s"""printf("$zoneName %llu %d\\n", ${zoneActTrackerName(zoneName)}, $zoneSize);"""
    }
  }

  def emitEvalTail(topName: String, circuit: Circuit) = {
    val simpleOnly = false
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
    val doNotDec = (regNames ++ (regNames map { _ + "$next" }) ++ (extIOs map { _._1 })).toSet
    val (allMemWrites, noMemWrites) = partitionByType[MemWrite](allBodies)
    val (printStmts, noPrints) = partitionByType[Print](noMemWrites)
    val stopStmts = noPrints flatMap findInstancesOf[Stop]
    val otherDeps = noPrints flatMap findDependencesStmt
    val memDeps = allMemWrites flatMap findDependencesStmt flatMap { _.deps }
    val memWritePorts = allMemWrites map { _.nodeName }
    val printDeps = printStmts flatMap findDependencesStmt flatMap { _.deps }
    val unsafeDepSet = (memDeps ++ printDeps).toSet
    val (unsafeRegs, safeRegs) = regNames partition { unsafeDepSet.contains(_) }
    println(s"${unsafeRegs.size} registers are deps for unmovable ops")
    writeLines(0, "")
    if (simpleOnly) {
      writeLines(0, s"} $topName;") //closing module dec (was done to enable predecs for zones)
      writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
      writeLines(1, "bool assert_triggered = false;")
      writeLines(1, "int assert_exit_code;")
    }
    // writeBodyUnopt(1, otherDeps, regNames)
    // writeBodyUnoptSG(1, noPrints, doNotDec)
    val doNotShadow = (regNames ++ memDeps ++ printDeps).distinct
    val keepAvail = (memDeps ++ printDeps).distinct
    // val doNotShadow = (regNames ++ memWritePorts ++ printDeps).distinct
    // val keepAvail = printDeps.distinct
    val mergedRegs = if (simpleOnly)
                       // writeBodyRegTailOptSG(1, noPrints, doNotDec, safeRegs)
                       // writeBodyMergeMWSG(1, noPrints, doNotDec, safeRegs, allMemWrites)
                       writeBodyMuxOptSG(1, noPrints, doNotShadow, doNotDec, safeRegs)
                       // writeBodyMuxOptMemSG(1, noPrints, doNotShadow, doNotDec, safeRegs, allMemWrites)
                     else
                       writeBodyZoneOptSG(noPrints, topName, allMemWrites, extIOs.toMap, regNames, keepAvail, doNotDec, safeRegs)
                       // writeBodyZoneOptSGMem(noPrints, topName, allMemWrites, extIOs.toMap, regNames, keepAvail, doNotDec, safeRegs)

    if (printStmts.nonEmpty || stopStmts.nonEmpty) {
      writeLines(1, "if (done_reset && update_registers) {")
      if (printStmts.nonEmpty) {
        writeLines(2, "if(verbose) {")
        writeLines(3, printStmts flatMap emitStmt(Set()))
        writeLines(2, "}")
      }
      if (stopStmts.nonEmpty) {
        writeLines(2, "if (assert_triggered) {")
        writeLines(3, "exit(assert_exit_code);")
        writeLines(2, "}")
      }
      writeLines(1, "}")
    }
    if (allRegDefs.nonEmpty || allMemWrites.nonEmpty) {
      writeLines(1, "if (update_registers) {")
      writeLines(2, allMemWrites flatMap emitStmt(Set()))
      // writeLines(2, allRegDefs map emitRegUpdate)
      writeLines(2, unsafeRegs ++ (safeRegs diff mergedRegs) map { regName => s"$regName = $regName$$next;" })
      writeLines(2, regResetOverrides(allRegDefs))
      if (!simpleOnly)
        writeLines(2, "regs_set = true;")
      writeLines(1, "}")
    }
    writeLines(0, "}")
    writeLines(0, "")
  }

  def writeEvalOuter(circuit: Circuit) {
    val optRegs = true
    val optMuxes = true
    val optZones = true
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
    val doNotDec = (regNames ++ (regNames map { _ + "$next" }) ++ (extIOs map { _._1 })).toSet
    val (allMemWrites, noMemWrites) = partitionByType[MemWrite](allBodies)
    val (printStmts, noPrints) = partitionByType[Print](noMemWrites)
    val stopStmts = noPrints flatMap findInstancesOf[Stop]
    val otherDeps = noPrints flatMap findDependencesStmt
    val memDeps = allMemWrites flatMap findDependencesStmt flatMap { _.deps }
    val memWritePorts = allMemWrites map { _.nodeName }
    val printDeps = printStmts flatMap findDependencesStmt flatMap { _.deps }
    val doNotShadow = (regNames ++ memWritePorts ++ printDeps).distinct
    val keepAvail = printDeps.distinct
    // val keepAvail = (memDeps ++ printDeps).distinct
    // val doNotShadow = (regNames ++ memDeps ++ printDeps).distinct
    val unsafeDepSet = (memDeps ++ printDeps).toSet
    val (unsafeRegs, safeRegs) = regNames partition { unsafeDepSet.contains(_) }
    println(s"${unsafeRegs.size} registers are deps for unmovable ops")
    val sg = StatementGraph(noPrints)
    sg.mergeMemWritesIntoSG(allMemWrites)
    if (optZones)
      sg.coarsenIntoZones(keepAvail)
    val mergedRegs = if (optRegs) {
                       if (optZones) sg.mergeRegUpdatesIntoZones(safeRegs)
                       else sg.mergeRegsSafe(safeRegs)
                     } else Seq()
    val unmergedRegs = regNames diff mergedRegs
    // FUTURE: worry about namespace collisions
    writeLines(1, "bool assert_triggered = false;")
    writeLines(1, "int assert_exit_code;")
    if (optZones) {
      writeZoningPredecs(sg, topName, allMemWrites, extIOs.toMap, regNames, mergedRegs, doNotDec, keepAvail)
    } else
      sg.updateMergedRegWrites(mergedRegs)
    if (!optZones) {
      writeLines(0, s"} $topName;") //closing module dec (was done to enable predecs for zones)
    }
    writeLines(0, "")
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    if (optZones)
      writeZoningBody(sg, regNames, unmergedRegs, allMemWrites, doNotDec)
    else
      writeBodyInner(1, sg, doNotDec, optMuxes, doNotShadow)
    if (printStmts.nonEmpty || stopStmts.nonEmpty) {
      writeLines(1, "if (done_reset && update_registers) {")
      if (printStmts.nonEmpty) {
        writeLines(2, "if(verbose) {")
        writeLines(3, printStmts flatMap emitStmt(Set()))
        writeLines(2, "}")
      }
      if (stopStmts.nonEmpty) {
        writeLines(2, "if (assert_triggered) {")
        writeLines(3, "exit(assert_exit_code);")
        writeLines(2, "}")
      }
      writeLines(1, "}")
    }
    if (allRegDefs.nonEmpty || allMemWrites.nonEmpty) {
      writeLines(1, "if (update_registers) {")
      // writeLines(2, allMemWrites flatMap emitStmt(Set()))
      writeLines(2, unsafeRegs ++ unmergedRegs map { regName => s"$regName = $regName$$next;" })
      writeLines(2, regResetOverrides(allRegDefs))
      if (optZones)
        writeLines(2, "regs_set = true;")
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
    writeEvalOuter(circuit)
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
    essent.passes.NoResetsOrClockConnects,
    essent.passes.RegFromMem1,
    essent.passes.FactorMemReads,
    essent.passes.FactorMemWrites,
    essent.passes.SplitRegUpdates,
    essent.passes.FixMulResultWidth)
    // passes.VerilogRename,
    // passes.VerilogPrep)
}

// TODO: use functionality within newer firrtl
class PrintCircuit extends Transform {
  def inputForm = MidForm
  def outputForm = LowForm
  def execute(state: CircuitState): CircuitState = {
    println(state.circuit.serialize)
    state
  }
}

class CCCompiler(verbose: Boolean, writer: Writer) extends Compiler {
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
    new FinalCleanups
  ) ++ (if (verbose) Seq(new PrintCircuit) else Seq())
}
