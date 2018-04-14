package essent

import collection.mutable.HashMap
import java.io.Writer

import essent.Emitter._
import essent.Extract._
import essent.ir._

import firrtl._
import firrtl.annotations._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.PrimOps._
import firrtl.Utils._


class EmitCpp(writer: Writer) {
  val tabs = "  "

  // Graph Building
  def buildGraph(hyperEdges: Seq[HyperedgeDep]) = {
    val g = new Graph
    hyperEdges foreach { he:HyperedgeDep =>
      g.addNodeWithDeps(he.name, he.deps)
    }
    g
  }


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
    }
    writeLines(0, s"} $modName;")
  }

  def declareExtModule(m: ExtModule) {
    val modName = m.name
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, m.ports flatMap emitPort(true))
    writeLines(0, s"} $modName;")
  }

  def buildResetTree(allInstances: Seq[(String, String)], circuit: Circuit): Seq[String] = {
    val instancesWithResets = allInstances filter { case (modName, prefix) => {
      findModule(modName, circuit).ports.exists{ _.name == "reset" }
    }}
    println(s"${instancesWithResets.size}/${allInstances.size} instances have resets")
    // TODO: is this correct? should map be { _._1 + _._2 }?
    val allInstanceNames = instancesWithResets.tail map { _._2 }
    val resetConnects = allInstanceNames map { fullModName: String => {
      val trailingDotRemoved = if (fullModName.contains(".")) fullModName.init
                               else fullModName
      val parentName = if (trailingDotRemoved.contains("."))
          trailingDotRemoved.substring(0, trailingDotRemoved.lastIndexOf(".")) + "."
        else ""
      Connect(NoInfo, WRef(s"${fullModName}reset", UIntType(IntWidth(1)), PortKind, FEMALE),
              WRef(s"${parentName}reset", UIntType(IntWidth(1)), PortKind, MALE))
    }}
    val allDeps = resetConnects flatMap findDependencesStmt
    val nameToStmt = (allDeps map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
    val reorderedConnectNames = buildGraph(allDeps).reorderNames
    reorderedConnectNames map nameToStmt flatMap emitStmt(Set())
  }

  // Vanilla emitter with no optimizations
  def writeBodyUnopt(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], regNames: Seq[String]) {
    // Simplified body, no mux shadowing
    val g = buildGraph(bodyEdges)
    // g.countChains()
    // g.writeDegreeFile(regNames, "rocketchip.degrees")
    // g.writeDotFile("rocketchip.dot")
    // g.writeMetisFile("rocketchip.metis")
    // g.scoutZones(regNames)
    // g.writeCOOFile("rocketchip.rcm.coo", Option(g.RCMordering()))
    val nameToStmt = (bodyEdges map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
    g.reorderNames foreach {
      name => writeLines(indentLevel, emitStmt(Set())(nameToStmt(name)))
    }
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

  def outputConsumerZones(zoneMap: Map[String, Graph.ZoneInfo]): Map[String, Seq[String]] = {
    val inputConsumerZonePairs = zoneMap.toSeq flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        inputs map { (_, zoneName) }
      }
    }
    inputConsumerZonePairs.groupBy(_._1).mapValues {
      pairs => pairs map { _._2 }
    }
  }

  def genFlagName(regName: String): String = s"ZONE_$regName".replace('.','$')

  def genDepZoneTriggers(consumers: Seq[String], condition: String) = {
    consumers map { consumer => s"${genFlagName(consumer)} |= $condition;" }
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
    val sg = StatementGraph(bodies)
    // val mergedRegs = sg.mergeRegsSafe(regsToConsider)
    sg.coarsenIntoZones(keepAvail)
    val mergedRegs = sg.mergeRegUpdatesIntoZones(regsToConsider)
    val mergedRegsSet = (mergedRegs map { _ + "$next"}).toSet
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
    sg.getSourceZone foreach { az => {
      println(s"There are ${az.memberNames.size} nodes in the SOURCE_ZONE")
      writeBodyMuxOptSG(1, az.memberStmts, keepAvail ++ regNames, doNotDec)
      // writeBodyUnoptSG(1, az.memberStmts, doNotDec ++ regNames)
    }}
    val zoneNames = sg.getZoneNames()
    writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    writeLines(0, s"bool sim_cached = false;")
    writeLines(0, s"bool regs_set = false;")

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
        if (az.name != "SOURCE_ZONE") {
          writeLines(1, s"if (${genFlagName(az.name)}) {")
          writeLines(2, s"${genFlagName(az.name)} = false;")
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
          writeLines(1, "}")
        }
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
    val regsTriggerZones = (regNames diff mergedRegs) flatMap { regName => {
      if (outputConsumers.contains(regName))
        genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
      else Seq()
    }}
    writeLines(1, regsTriggerZones)
    mergedRegs
  }

  def checkZoningSanity(
      sg: StatementGraph,
      memWrites: Seq[MemWrite],
      extIOtypes: Map[String, Type],
      regNames: Seq[String],
      keepAvail: Seq[String]): Boolean = {
    // GOAL: make sure every input on every zone gets a trigger
    // possible stretch goal: ensure unzoned values given fresh values to compare
    // possible stretch goal: make sure trigger ordering is appropriate
    // Generate all triggers
    val outputPairs = sg.getZoneOutputTypes()
    val outputConsumers = sg.getZoneInputMap()
    val doNotDec = (outputPairs map { _._1 }).toSet
    val otherInputs = sg.getExternalZoneInputs() diff regNames
    val memNames = (memWrites map { _.memName }).toSet
    val (memInputs, nonMemInputs) = otherInputs partition { memNames.contains(_) }
    val nonMemTriggers = nonMemInputs flatMap { sigName => {
      outputConsumers(sigName) flatMap { zoneName => Seq((sigName, zoneName) -> "PRE-nonMem") }
    }}
    val fromZoneTriggers = sg.stmtsOrdered flatMap { stmt => stmt match {
      case az: ActivityZone => {
        val outputTriggers = az.outputConsumers.toSeq flatMap {
          case (name, consumers) => consumers flatMap {
            zoneName => Seq((name, zoneName) -> az.name)
          }
        }
        outputTriggers
        // TODO: merged regs triggers
      }
      case _ => Seq()
    }}
    val memTriggers = memInputs.toSeq flatMap { memName => {
      outputConsumers(memName) flatMap { zoneName => Seq((memName, zoneName) -> "POST-mem") }
    }}
    val globalRegTriggers = regNames flatMap { regName => {
      if (outputConsumers.contains(regName)) {
        outputConsumers(regName) flatMap { zoneName => Seq((regName, zoneName) -> "POST-reg") }
      } else Seq()
    }}
    val inputZonePairToTriggerSource = (nonMemTriggers ++ fromZoneTriggers ++ memTriggers ++ globalRegTriggers).toMap

    // For each zone, verify all inputs have a trigger
    val allZoneInputs = sg.stmtsOrdered flatMap { stmt => stmt match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}
    if (inputZonePairToTriggerSource.size != allZoneInputs.size)
      println(s"MISMATCH: ${inputZonePairToTriggerSource.size} triggers for ${allZoneInputs.size} inputs")
    val allTriggersFound = sg.stmtsOrdered forall { stmt => stmt match {
      case az: ActivityZone => {
        val allInputsHaveTriggers = az.inputs forall {
          inputName => inputZonePairToTriggerSource.contains((inputName, az.name))
        }
        if (!allInputsHaveTriggers)
          println(s"zone ${az.name} has incomplete set of triggers")
        allInputsHaveTriggers
      }
      case _ => true
    }}
    println(s"all triggers found: $allTriggersFound")
    allTriggersFound
  }

  def printZoneStateAffinity(zoneMap: Map[String,Graph.ZoneInfo],
                             regNames: Seq[String], memWrites: Seq[MemWrite]) {
    val regNamesSet = regNames.toSet
    val regNameZoneNamePairs = zoneMap.toSeq flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        val regInputs = inputs.toSet.intersect(regNamesSet)
        regInputs.toSeq map { regInput => (regInput, zoneName) }
      }
    }
    val regToConsumingZones = regNameZoneNamePairs.groupBy(_._1)
    val regToNumZones = regToConsumingZones map {
      case (regName, zoneNamePairs) => (regName, zoneNamePairs.size)
    }
    println("Histogram of number of zones consume a register:")
    println(regToNumZones.values.groupBy(identity).mapValues(_.size))
    val sigNameZoneMap = (zoneMap.toSeq flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        members map { (_, zoneName) }
      }
    }).toMap
    val numProducingZones = memWrites map { mw => {
      val deps = findDependencesStmt(mw).head.deps
      val depsFromZones = deps filter {sigNameZoneMap.contains(_) }
      val numProducingZones = (depsFromZones map sigNameZoneMap).distinct.size
      numProducingZones
    }}
    println("Histogram of number of zones producing signals for mem write:")
    println(numProducingZones.groupBy(identity).mapValues(_.size))
    val includedRegWrites = regNames filter {regName => sigNameZoneMap.contains(regName + "$next") }
    println(s"${includedRegWrites.size}/${regNames.size} registers have zone for $$next")
    val regsInLoopbackZones = includedRegWrites filter { regName => {
      val writeZone = sigNameZoneMap(regName + "$next")
      zoneMap(writeZone).inputs.contains(regName)
    }}
    println(s"${regsInLoopbackZones.size} registers have same zone input and output")
  }

  def findZoneDescendants(inSignals: Set[String], zoneMap: Map[String, Graph.ZoneInfo]): Seq[String] = {
    val childZones = zoneMap flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        if (inputs exists inSignals) Seq(zoneName)
        else Seq()
      }
    }
    println(s"CZ size ${childZones.size}")
    val childZonesSet = childZones.toSet
    val nextInSignals = inSignals ++ (zoneMap flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        if (childZonesSet.contains(zoneName)) outputs
        else Seq()
    }}).toSet
    if (inSignals == nextInSignals) childZones.toSeq
    else findZoneDescendants(nextInSignals, zoneMap)
  }

  def decRegActivityTracking(regNames: Seq[String]) = {
    regNames foreach { regName => {
      val noDotsInName = regName.replace('.', '$')
      writeLines(0, s"uint64_t $noDotsInName$$trans = 0;")
    }}
  }

  def recRegActivityTracking(regNames: Seq[String]) = {
    regNames foreach { regName => {
      val noDotsInName = regName.replace('.', '$')
      writeLines(2, s"if ($regName != ${regName}$$next) $noDotsInName$$trans++;")
    }}
  }

  def printRegActivityTracking(regNames: Seq[String]) = {
    writeLines(0, "void print_activity() {")
    regNames foreach { regName => {
      val noDotsInName = regName.replace('.', '$')
      writeLines(1, s"""printf("$regName %llu\\n", $noDotsInName$$trans);""")
    }}
    writeLines(0, "}")
  }

  def writeRegActivityTracking(regNames: Seq[String]) {
    writeLines(2, s"const uint64_t num_regs = ${regNames.size};")
    writeLines(2, s"uint64_t transitions = 0;")
    writeLines(2, s"cycles_ticked++;")
    regNames foreach { regName =>
      writeLines(2, s"if ($regName != ${regName}$$next) transitions++;")
    }
    writeLines(2, "total_transitions += transitions;")
    writeLines(2, s"""printf("Transitions %llu/%llu\\n", transitions, num_regs);""")
    writeLines(2, s"""printf("Average Active: %g\\n", (double) total_transitions/cycles_ticked);""")
  }

  def writeZoneActivityTracking(zoneNames: Seq[String]) {
    writeLines(2, s"const uint64_t num_zones = ${zoneNames.size};")
    writeLines(2, s"uint64_t zones_active = 0;")
    zoneNames foreach { zoneName =>
      writeLines(2, s"if (${genFlagName(zoneName)}) zones_active++;")
    }
    writeLines(2, s"total_zones_active += zones_active;")
    writeLines(2, s"""printf("Zones Active %llu/%llu\\n", zones_active, num_zones);""")
    writeLines(2, s"""printf("Average Zones: %g\\n", (double) total_zones_active/cycles_ticked);""")
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
    val printDeps = printStmts flatMap findDependencesStmt flatMap { _.deps }
    val unsafeDepSet = (memDeps ++ printDeps).toSet
    val (unsafeRegs, safeRegs) = regNames partition { unsafeDepSet.contains(_) }
    println(s"${unsafeRegs.size} registers are deps for unmovable ops")
    writeLines(0, "")
    if (simpleOnly) {
      writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
      writeLines(1, "bool assert_triggered = false;")
      writeLines(1, "int assert_exit_code;")
    }
    // writeBodyUnopt(1, otherDeps, regNames)
    // writeBodyUnoptSG(1, allBodies, doNotDec)
    val doNotShadow = (regNames ++ memDeps ++ printDeps).distinct
    val keepAvail = (memDeps ++ printDeps).distinct
    val mergedRegs = if (simpleOnly)
                       // writeBodyRegTailOptSG(1, allBodies, doNotDec, safeRegs)
                       writeBodyMuxOptSG(1, allBodies, doNotShadow, doNotDec, safeRegs)
                     else
                       writeBodyZoneOptSG(allBodies, topName, allMemWrites, extIOs.toMap, regNames, keepAvail, doNotDec, safeRegs)
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
    emitEvalTail(topName, circuit)
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
