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
  def separatePrintsAndStops(deps: Seq[HyperedgeDep]) = {
    val (printsAndStops, otherDeps) = deps.partition { dep => dep.stmt match {
      case p: Print => true
      case s: Stop => true
      case _ => false
    }}
    val (prints, stops) = printsAndStops partition { dep => dep.stmt match {
      case p: Print => true
      case _ => false
    }}
    (otherDeps, prints, stops)
  }

  def buildGraph(hyperEdges: Seq[HyperedgeDep]) = {
    val g = new Graph
    hyperEdges foreach { he:HyperedgeDep =>
      g.addNodeWithDeps(he.name, he.deps)
    }
    g
  }

  def addMemDepsToGraph(g: Graph, memUpdates: Seq[MemUpdate]) {
    // FUTURE: does not handle multiple write ports to same mem
    memUpdates foreach {
      mu => g.addNodeWithDeps(mu.memName + "$next", findDependencesMemWrite(mu))
    }
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

  // Emitter that performs single-phase reg updates (merges) when possible, and returns merged regs
  def writeBodyRegTailOpt(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], regNames: Seq[String]): Seq[String] = {
    val nameToStmt = (bodyEdges map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
    val g = buildGraph(bodyEdges)
    val mergedRegs = g.mergeRegsSafe(regNames)
    val mergedRegWrites = (mergedRegs map { _ + "$next" }).toSet
    g.reorderNames foreach { name => {
      if (mergedRegWrites.contains(name)) {
        val emitted = emitStmt(Set())(nameToStmt(name)).head
        val replaced = emitted.replaceAllLiterally("$next", "")
        writeLines(indentLevel, "if (update_registers) " + replaced)
      } else {
        writeLines(indentLevel, emitStmt(Set())(nameToStmt(name)))
      }
    }}
    mergedRegs
  }

  def writeBodyRegTailOptSG(indentLevel: Int, bodies: Seq[Statement], doNotDec: Set[String], regNames: Seq[String]): Seq[String] = {
    val sg = StatementGraph(bodies)
    val mergedRegs = sg.mergeRegsSafe(regNames)
    sg.updateMergedRegWrites(mergedRegs)
    sg.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(doNotDec)(stmt)) }
    mergedRegs
  }

  // Emitter that shadows muxes in addition to single-phase reg updates
  def writeBodyMuxOpt(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], doNotShadow: Seq[String],
      doNotDec: Set[String], regsToConsider: Seq[String]=Seq()): Seq[String] = {
    if (bodyEdges.nonEmpty) {
      // name to mux expression
      val muxMap = findMuxExpr(bodyEdges).toMap
      val shadows = buildGraph(bodyEdges).findAllShadows(muxMap, doNotShadow)
      // map of muxName -> true shadows, map of muxName -> false shadows
      val trueShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, tShadow)}).toMap
      val falseShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, fShadow)}).toMap
      // only shadow mux if stuff on at least one side
      val shadowedMuxes = (muxMap.keys filter {
        muxName => trueShadows(muxName).nonEmpty || falseShadows(muxName).nonEmpty
      }).toSet
      // set of signals in shadows
      val shadowedSigs = (shadows flatMap { case (muxName, tShadow, fShadow) => {
        if (shadowedMuxes.contains(muxName)) tShadow ++ fShadow
        else Seq()
      }}).toSet
      if (indentLevel == 1) println(s"Total shadow size: ${shadowedSigs.size}")
      // map of name -> original hyperedge
      val heMap = (bodyEdges map { he => (he.name, he) }).toMap
      // top level edges (filter out shadows) & make muxes depend on shadow inputs
      val unshadowedHE = bodyEdges filter {he => !shadowedSigs.contains(he.name)}
      val topLevelHE = unshadowedHE map { he => {
        val deps = if (!shadowedMuxes.contains(he.name)) he.deps
                   else {
                     val shadowDeps = (trueShadows(he.name) ++ falseShadows(he.name)) flatMap { heMap(_).deps }
                     he.deps ++ shadowDeps
                   }
        // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
        he.copy(deps = deps.distinct)
      }}
      // build graph on new hyperedges and run topo sort
      val g = buildGraph(topLevelHE)
      val mergedRegs = g.mergeRegsSafe(regsToConsider)
      val mergedRegWrites = (mergedRegs map { _ + "$next" }).toSet
      // Assuming if replacing, only one statement has name, otherwise extra if (upda..
      def mergeRegUpdateIfPossible(name: String, toEmit: String): String = {
        val removed = toEmit.replaceAllLiterally("$next", "")
        if (mergedRegWrites.contains(name)) "if (update_registers) " + removed
        else toEmit
      }
      g.reorderNames foreach { name => {
        val stmt = heMap(name).stmt
        if (shadowedMuxes.contains(name)) {
          def writeShadow(members: Seq[String], muxValExpr: Expression) {
            // NOTE: not calling writeBodyMuxOpt since regs can't be in shadows
            writeBodyMuxOpt(indentLevel + 1, members map heMap, doNotShadow, doNotDec)
            writeLines(indentLevel + 1, mergeRegUpdateIfPossible(name, s"$name = ${emitExpr(muxValExpr)};"))
          }
          val muxExpr = muxMap(name)
          // declare output type
          val resultTpe = findResultType(stmt)
          // FUTURE: don't require finding $next in name, change caller to adjust doNotDec
          if ((!name.endsWith("$next")) && (!doNotDec.contains(name)))
            writeLines(indentLevel, s"${genCppType(resultTpe)} $name;")
          writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
          writeShadow(trueShadows(name), muxExpr.tval)
          writeLines(indentLevel, "} else {")
          writeShadow(falseShadows(name), muxExpr.fval)
          writeLines(indentLevel, "}")
        } else {
          writeLines(indentLevel, emitStmt(doNotDec)(stmt) map {mergeRegUpdateIfPossible(name, _)})
        }
      }}
      mergedRegs
    } else Seq()
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
          if ((!ms.name.endsWith("$next")) && (!doNotDec.contains(ms.name)) && (!ms.name.contains("if (update_registers)")))
            writeLines(indentLevel, s"${genCppType(ms.mux.tpe)} ${ms.name};")
          writeLines(indentLevel, s"if (${emitExpr(ms.mux.cond)}) {")
          writeBodyMuxOptSG(indentLevel + 1, ms.tShadow, doNotShadow, doNotDec)
          writeLines(indentLevel + 1, s"${ms.name} = ${emitExpr(ms.mux.tval)};")
          writeLines(indentLevel, "} else {")
          writeBodyMuxOptSG(indentLevel + 1, ms.fShadow, doNotShadow, doNotDec)
          writeLines(indentLevel + 1, s"${ms.name} = ${emitExpr(ms.mux.fval)};")
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

  // Emitter that zones design in addition to shadowing muxes and merging reg updates
  def writeBodyZoneOpt(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String], resetTree: Seq[String],
                           topName: String, doNotShadow: Seq[String], memUpdates: Seq[MemUpdate],
                           extIOtypes: Map[String, Type], regsToConsider: Seq[String]): Seq[String] = {
    // map of name -> original hyperedge
    val heMap = (bodyEdges map { he => (he.name, he) }).toMap
    val regNamesSet = regNames.toSet
    // calculate zones based on all edges
    val g = buildGraph(bodyEdges)
    g.printTopologyStats
    val mergedRegs = g.mergeRegsSafe(regsToConsider)
    val zoneMapWithSources = g.findZonesMFFC(doNotShadow)
    val zoneMapCF = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
    val gDF = buildGraph(bodyEdges)
    val zoneMapDF = gDF.remakeZoneMap(zoneMapCF, doNotShadow)
    gDF.analyzeZoningQuality(zoneMapDF)
    val inputsToZones = zoneMapDF.flatMap(_._2.inputs).toSet
    val nodesInZones = zoneMapDF.flatMap(_._2.members).toSet
    val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
    val outputsFromZones = zoneMapDF.flatMap(_._2.outputs).toSet.diff(regNamesSet)
    val outputConsumers = outputConsumerZones(zoneMapDF)
    val inputRegs = (regNamesSet intersect inputsToZones).toSeq
    val mergedInRegs = (mergedRegs intersect inputRegs filter { outputConsumers.contains(_) })
    val regsUncheckedByZones = inputRegs diff mergedInRegs
    val shouldCheckInZone = (mergedInRegs map { _ + "$next"}).toSet
    val shouldSetInZone = (mergedRegs map { _ + "$next"}).toSet

    // predeclare output nodes
    val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
    val outputPairs = (outputTypes zip outputsFromZones).toSeq
    val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
    writeLines(0, preDecs)
    val doNotDec = outputsFromZones.toSet
    println(s"Output nodes: ${outputsFromZones.size}")

    // set input flags to true for other inputs (resets, mems, or external IOs)
    // FUTURE: remove. should make change detection for these inputs so consuming
    //         zones have a chance to sleep
    val otherFlags = inputsToZones diff (regNamesSet ++ zoneMapWithSources.flatMap(_._2.outputs).toSet)
    val memNames = memUpdates map { _.memName }
    val memFlags = otherFlags intersect memNames.toSet
    val nonMemFlags = otherFlags diff memNames.toSet
    // FUTURE: fix, can't be hacking for reset, but reset isn't in signal map table
    val nonMemFlagTypes = nonMemFlags.toSeq map {
      name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
    }
    val nonMemPreDecs = (nonMemFlagTypes zip nonMemFlags.toSeq) map {
      case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(0, nonMemPreDecs)

    // predeclare zone activity flags
    val zoneNames = zoneMapCF.keys.toSeq
    writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
    println(s"Activity flags: ${zoneNames.size}")

    writeLines(0, s"bool sim_cached = false;")
    writeLines(0, s"bool regs_set = false;")

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, resetTree)

    writeLines(1, "if (!sim_cached) {")
    writeLines(2, zoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
    writeLines(1, "}")
    writeLines(1, "sim_cached = regs_set;")

    // do activity detection on other inputs (external IOs and resets)
    val nonMemChangeDetects = nonMemFlags flatMap { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      genDepZoneTriggers(outputConsumers(sigName), s"$sigName != $oldVersion")
    }}
    writeLines(1, nonMemChangeDetects.toSeq)
    // cache old versions
    val nonMemCaches = nonMemFlags map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)

    // compute zone order
    // map of name -> zone name (if in zone)
    val nameToZoneName = zoneMapCF flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        outputs map { portName => (portName, zoneName) }
    }}
    // list of super hyperedges for zones
    val zoneSuperEdges = zoneMapCF map {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        HyperedgeDep(zoneName, inputs, heMap(members.head).stmt)
    }}
    // list of non-zone hyperedges
    val nonZoneEdges = bodyEdges filter { he => !nodesInZonesWithSources.contains(he.name) }
    // list of hyperedges with zone members replaced with zone names
    val topLevelHE = zoneSuperEdges map { he:HyperedgeDep => {
      val depsRenamedForZones = (he.deps map {
        depName => nameToZoneName.getOrElse(depName, depName)
      }).distinct
      HyperedgeDep(he.name, depsRenamedForZones, he.stmt)
    }}
    // reordered names
    val gTopLevel = buildGraph(topLevelHE.toSeq)
    val zonesReordered = gTopLevel.reorderNames

    // emit zone of sources
    if (zoneMapWithSources.contains("ZONE_SOURCE")) {
      val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
      val sourceZoneEdges = sourceZoneInfo.members map heMap
      // FUTURE: does this need to be made into tail?
      writeBodyMuxOpt(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
    }

    // emit each zone
    zonesReordered map { zoneName => (zoneName, zoneMapDF(zoneName)) } foreach {
        case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
      writeLines(1, s"if (${genFlagName(zoneName)}) {")
      writeLines(2, s"${genFlagName(zoneName)} = false;")
      val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
      val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
      val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
        s"${genCppType(tpe)} $name$$old = $name;"
      }}
      writeLines(2, oldOutputs)
      val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
      // FUTURE: shouldn't this be made into tail?
      writeBodyMuxOpt(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
      val regsInZone = members filter shouldCheckInZone map { _.replaceAllLiterally("$next","") }
      val regsTriggerZones = regsInZone flatMap {
        regName => genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
      }
      writeLines(2, regsTriggerZones)
      val outputTriggers = outputsCleaned flatMap {
        name => genDepZoneTriggers(outputConsumers(name), s"$name != $name$$old")
      }
      writeLines(2, outputTriggers)
      val regsToUpdate = members filter shouldSetInZone map { _.replaceAllLiterally("$next","") }
      writeLines(2, regsToUpdate map { regName => s"$regName = $regName$$next;" })
      writeLines(1, "}")
    }}

    // emit rest of body (without redeclaring)
    // FUTURE: does this need to be made into tail?
    writeBodyMuxOpt(1, nonZoneEdges, doNotShadow, doNotDec)

    // trigger zones based on mem writes
    // NOTE: if mem has multiple write ports, either can trigger wakeups
    val memEnablesAndMasks = (memUpdates map {
      mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
    }).toMap
    val memWriteTriggerZones = memFlags.toSeq flatMap { flagName => {
      val condition = memEnablesAndMasks(flagName).mkString(" && ");
      genDepZoneTriggers(outputConsumers(flagName), condition)
    }}
    writeLines(1, memWriteTriggerZones)

    val regsTriggerZones = regsUncheckedByZones.toSeq flatMap { regName => {
      if (outputConsumers.contains(regName))
        genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
      else Seq()
    }}
    writeLines(1, regsTriggerZones)
    mergedRegs
  }

  def writeBodyZoneOptSG(
      bodies: Seq[Statement],
      topName: String,
      resetTree: Seq[String],
      memUpdates: Seq[MemUpdate],
      extIOtypes: Map[String, Type],
      regNames: Seq[String],
      keepAvail: Seq[String],
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
    val doNotDec = ((outputPairs map { _._1 }) ++ regNames).toSet
    val otherInputs = sg.getExternalZoneInputs() diff regNames
    val memNames = (memUpdates map { _.memName }).toSet
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

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, "if (reset || !done_reset) {")
    writeLines(2, "sim_cached = false;")
    writeLines(2, "regs_set = false;")
    writeLines(1, "}")
    writeLines(1, resetTree)
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
        if (az.name == "SOURCE_ZONE") {
          println(s"There are ${az.memberNames.size} nodes in the SOURCE_ZONE")
          writeBodyMuxOptSG(1, az.memberStmts, keepAvail ++ regNames, doNotDec)
          // writeBodyUnoptSG(1, az.memberStmts, doNotDec ++ regNames)
        } else {
          writeLines(1, s"if (${genFlagName(az.name)}) {")
          writeLines(2, s"${genFlagName(az.name)} = false;")
          val cacheOldOutputs = az.outputTypes.toSeq map {
            case (name, tpe) => { s"${genCppType(tpe)} $name$$old = $name;"
          }}
          writeLines(2, cacheOldOutputs)
          writeBodyMuxOptSG(2, az.memberStmts, keepAvail ++ regNames ++ doNotDec, doNotDec)
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
          writeLines(1, "}")
        }
      }
      case _ => writeLines(1, emitStmt(doNotDec)(stmt))
    }}
    // trigger zones based on mem writes
    // NOTE: if mem has multiple write ports, either can trigger wakeups
    val memEnablesAndMasks = (memUpdates map {
      mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
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
      memUpdates: Seq[MemUpdate],
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
    val memNames = (memUpdates map { _.memName }).toSet
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
                             regNames: Seq[String], memUpdates: Seq[MemUpdate]) {
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
    val numProducingZones = memUpdates map { mu => {
      val deps = Seq(mu.wrEnName, mu.wrMaskName, mu.wrAddrName, mu.wrDataName)
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
    val extIOs = allInstances flatMap {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => None
        case em: ExtModule => em.ports map { port => (s"$prefix${port.name}", port.tpe) }
      }
    }
    val resetTree = buildResetTree(allInstances, circuit)
    val allMemUpdates = generateMemUpdates(allBodies)
    val allRegDefs = allBodies flatMap findRegisters
    val allDeps = allBodies flatMap findDependencesStmt
    val (otherDeps, prints, stops) = separatePrintsAndStops(allDeps)
    val regNames = allRegDefs map { _.name }
    val memDeps = allMemUpdates flatMap findDependencesMemWrite
    val pAndSDeps = (prints ++ stops) flatMap { he => he.deps }
    val unsafeRegs = regNames.intersect(memDeps ++ pAndSDeps)
    val safeRegs = regNames diff unsafeRegs
    println(s"${unsafeRegs.size} registers are deps for unmovable ops")
    writeLines(0, "")
    if (simpleOnly) {
      writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
      writeLines(1, resetTree)
    }
    // writeBodyUnopt(1, otherDeps, regNames)
    // writeBodyUnoptSG(1, allBodies)
    val doNotShadow = (regNames ++ memDeps ++ pAndSDeps).distinct
    val keepAvail = (memDeps ++ pAndSDeps).distinct
    val mergedRegs = if (simpleOnly)
                       // writeBodyRegTailOpt(1, otherDeps, safeRegs)
                       // writeBodyRegTailOptSG(1, allBodies, safeRegs)
                       // writeBodyMuxOpt(1, otherDeps, doNotShadow, regNames.toSet, safeRegs)
                       writeBodyMuxOptSG(1, allBodies, doNotShadow, regNames.toSet, safeRegs)
                     else
                       writeBodyZoneOptSG(allBodies, topName, resetTree, allMemUpdates, extIOs.toMap, regNames, keepAvail, safeRegs)
                       // writeBodyZoneOpt(otherDeps, regNames, resetTree, topName, doNotShadow,
                       //    allMemUpdates, extIOs.toMap, safeRegs)
    if (prints.nonEmpty || stops.nonEmpty) {
      writeLines(1, "if (done_reset && update_registers) {")
      if (prints.nonEmpty) {
        writeLines(2, "if(verbose) {")
        writeLines(3, (prints map {dep => dep.stmt} flatMap emitStmt(Set())))
        writeLines(2, "}")
      }
      writeLines(2, (stops map {dep => dep.stmt} flatMap emitStmt(Set())))
      writeLines(1, "}")
    }
    if (allRegDefs.nonEmpty || allMemUpdates.nonEmpty) {
      writeLines(1, "if (update_registers) {")
      writeLines(2, allMemUpdates map emitMemUpdate)
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
    // writeLines(0, "#include <gmpxx.h>")
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
    essent.passes.SplitRegUpdates)
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
