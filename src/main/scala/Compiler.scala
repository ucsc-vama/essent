package essent

import collection.mutable.HashMap
import java.io.Writer

import essent.Emitter._
import essent.Extract._

import firrtl._
import firrtl.Annotations._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes.bitWidth
import firrtl.PrimOps._
import firrtl.Utils._


class EmitCpp(writer: Writer) extends Transform {
  val tabs = "  "

  // Graph Building
  def findDependencesExpr(e: Expression): Seq[String] = {
    val result = e match {
      case w: WRef => {
        if (w.name.contains('[')) {
          val deps = w.name.split('[').toSeq.map(_.replaceFirst(""".as_single_word\(\)\]""",""))
          deps filter { !_.contains("Int<") } // remove literals
        } else Seq(w.name)
      }
      case m: Mux => Seq(m.cond, m.tval, m.fval) flatMap findDependencesExpr
      case w: WSubField => Seq(emitExpr(w))
      case p: DoPrim => p.args flatMap findDependencesExpr
      case u: UIntLiteral => Seq()
      case s: SIntLiteral => Seq()
      case _ => throw new Exception("unexpected expression type! " + e)
    }
    result.distinct map grabMemAddr
  }

  def findDependencesStmt(s: Statement): Seq[HyperedgeDep] = s match {
    case b: Block => b.stmts flatMap findDependencesStmt
    case d: DefNode => Seq(HyperedgeDep(d.name, findDependencesExpr(d.value), s))
    case c: Connect => {
      val lhs = emitExpr(c.loc)
      val rhs = findDependencesExpr(c.expr)
      firrtl.Utils.kind(c.loc) match {
        case firrtl.MemKind => Seq()
        case firrtl.RegKind => Seq(HyperedgeDep(lhs + "$next", rhs, s))
        case _ => Seq(HyperedgeDep(lhs, rhs, s))
      }
    }
    case p: Print =>
      Seq(HyperedgeDep("printf", findDependencesExpr(p.en) ++
                                 (p.args flatMap findDependencesExpr), s))
    case st: Stop => Seq(HyperedgeDep("stop", findDependencesExpr(st.en), st))
    case r: DefRegister => Seq()
    case w: DefWire => Seq()
    case m: DefMemory => Seq()
    case i: WDefInstance => Seq()
    case EmptyStmt => Seq()
    case _ => throw new Exception(s"unexpected statement type! $s")
  }

  def findDependencesMemWrite(emittedCmd: String): Seq[String] = {
    val insideIf = "([(].*[)]) ".r.findAllIn(emittedCmd).toList.head.tail.init.init
    val enAndMask = insideIf.split(" && ")
    val memAndAddr = emittedCmd.split("=").head.trim.split(" ").last.init.split('[').map(_.replaceFirst(""".as_single_word\(\)""",""))
    val dataName = emittedCmd.split("=").last.trim.init
    val deps = enAndMask.toSeq ++ memAndAddr.toSeq ++ Seq(dataName)
    deps filter { name: String => !name.startsWith("UInt<1>(0x") }
  }

  def findDependencesMemWrite(mu: MemUpdate): Seq[String] = {
    val deps = Seq(mu.wrEnName, mu.wrMaskName, mu.wrAddrName, mu.wrDataName)
    deps filter { name => !name.startsWith("UInt<1>(0x") }
  }

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
      writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
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

  def buildResetTree(allInstances: Seq[(String, String)]): Seq[String] = {
    val allInstanceNames = allInstances.tail map { _._2 }
    val resetConnects = allInstanceNames map { modName: String => {
      val trailingDotRemoved = if (modName.contains(".")) modName.init
                               else modName
      val parentName = if (trailingDotRemoved.contains("."))
          trailingDotRemoved.substring(0, trailingDotRemoved.lastIndexOf(".")) + "."
        else ""
      Connect(NoInfo, WRef(s"${modName}reset", UIntType(IntWidth(1)), PortKind, FEMALE),
              WRef(s"${parentName}reset", UIntType(IntWidth(1)), PortKind, MALE))
    }}
    val allDeps = resetConnects flatMap findDependencesStmt
    val nameToStmt = (allDeps map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
    val reorderedConnectNames = buildGraph(allDeps).reorderNames
    reorderedConnectNames map nameToStmt flatMap emitStmt(Set())
  }

  def writeBodySimple(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], regNames: Seq[String]) {
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

  def writeBody(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], doNotShadow: Seq[String],
      doNotDec: Set[String]) {
    if (!bodyEdges.isEmpty) {
      // val muxOutputNames = findMuxOutputNames(bodyEdges)
      // name to mux expression
      val muxMap = findMuxExpr(bodyEdges).toMap
      val shadows = buildGraph(bodyEdges).findAllShadows(muxMap, doNotShadow)
      // map of muxName -> true shadows, map of muxName -> false shadows
      val trueShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, tShadow)}).toMap
      val falseShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, fShadow)}).toMap
      // set of signals in shadows
      val shadowedSigs = (shadows flatMap {
        case (muxName, tShadow, fShadow) => (tShadow ++ fShadow) }).toSet
      if (indentLevel == 1) println(s"Total shadow size: ${shadowedSigs.size}")
      // map of name -> original hyperedge
      val heMap = (bodyEdges map { he => (he.name, he) }).toMap
      // top level edges (filter out shadows) & make muxes depend on shadow inputs
      val unshadowedHE = bodyEdges filter {he => !shadowedSigs.contains(he.name)}
      val topLevelHE = unshadowedHE map { he => {
        val deps = if (!trueShadows.contains(he.name)) he.deps
                   else {
                     val shadowDeps = (trueShadows(he.name) ++ falseShadows(he.name)) flatMap { heMap(_).deps }
                     he.deps ++ shadowDeps
                   }
        // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
        HyperedgeDep(he.name, deps.distinct, he.stmt)
      }}
      // build graph on new hyperedges and run topo sort
      val reorderedNames = buildGraph(topLevelHE).reorderNames
      reorderedNames foreach { name => {
        val stmt = heMap(name).stmt
        if ((trueShadows.contains(name)) && ((!trueShadows(name).isEmpty) || (!falseShadows(name).isEmpty))) {
          val muxExpr = muxMap(name)
          // declare output type
          val resultTpe = findResultType(stmt)
          if ((!name.endsWith("$next")) && (!doNotDec.contains(name)))
            writeLines(indentLevel, s"${genCppType(resultTpe)} $name;")
          writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
          val trueHE = trueShadows(name) map { heMap(_) }
          writeBody(indentLevel + 1, trueHE, doNotShadow, doNotDec)
          writeLines(indentLevel + 1, s"$name = ${emitExpr(muxExpr.tval)};")
          writeLines(indentLevel, "} else {")
          val falseHE = falseShadows(name) map { heMap(_) }
          writeBody(indentLevel + 1, falseHE, doNotShadow, doNotDec)
          writeLines(indentLevel + 1, s"$name = ${emitExpr(muxExpr.fval)};")
          writeLines(indentLevel, "}")
        } else writeLines(indentLevel, emitStmt(doNotDec)(stmt))
      }}
    }
  }

  def genFlagName(regName: String): String = s"ZONE_$regName".replace('.','$')

  def genFlagName(regName: String, renames: Map[String, String]): String = {
    genFlagName(renames.getOrElse(regName, regName))
  }

  def writeBodyWithZones(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
                         allRegUpdates: Seq[String], resetTree: Seq[String],
                         topName: String, otherDeps: Seq[String],
                         doNotShadow: Seq[String]) {
    val trackActivity = false
    // map of name -> original hyperedge
    val heMap = (bodyEdges map { he => (he.name, he) }).toMap
    // calculate zones based on all edges
    val allZones = buildGraph(bodyEdges).findZones(regNames)
    val zoneMap = allZones filter { case (k,v) => v.size > 10}
    // set of all nodes in zones
    val nodesInZones = zoneMap.values.flatten.toSet
    println(s"Nodes in zones: ${nodesInZones.size}")
    // map of zone name -> zone edges (easy) - needed?
    val zoneEdges = zoneMap map {case (k,v) => (k, v filter {heMap.contains} map {heMap})}
    // seq of edges not in zones
    val nonZoneEdges = bodyEdges filter { he => !nodesInZones.contains(he.name) }
    // set of all dependences from non-zone edges
    val nonZoneDeps = (nonZoneEdges map { _.deps }).flatten.toSet ++ otherDeps.toSet
    // output nodes (intersection of deps and zone nodes)
    val zoneOutputs = nonZoneDeps.intersect(nodesInZones) filter {!regNames.contains(_)}
    val doNotDec = zoneOutputs.toSet
    // predeclare output nodes
    val outputTypes = zoneOutputs.toSeq map {name => findResultType(heMap(name).stmt)}
    val outputPairs = (outputTypes zip zoneOutputs).toSeq
    val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
    writeLines(0, preDecs)
    // activity tracking
    if (trackActivity) {
      writeLines(0, "uint64_t total_transitions = 0;")
      writeLines(0, "uint64_t total_zones_active = 0;")
      writeLines(0, "uint64_t cycles_ticked = 0;")
    }
    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, resetTree)
    // predeclare zone activity flags
    writeLines(1, (zoneMap.keys map { zoneName => s"bool ${genFlagName(zoneName)} = reset;"}).toSeq)
    // emit update checks
    zoneMap foreach { case (zoneName, zoneContents) => {
      writeLines(1, s"if ($zoneName != $zoneName$$next) ${genFlagName(zoneName)} = true;")
      zoneContents filter { name => regNames.contains(name) } foreach { name =>
        writeLines(1, s"if ($name != $name$$next) ${genFlagName(zoneName)} = true;")}
    }}
    // emit reg updates
    if (!allRegUpdates.isEmpty || trackActivity) {
      writeLines(1, "if (update_registers) {")
      if (trackActivity) {
        writeRegActivityTracking(regNames)
        writeZoneActivityTracking(zoneMap.keys.toSeq)
      }
      writeLines(2, allRegUpdates)
      writeLines(1, "}")
    }
    // emit each zone
    zoneMap.keys foreach { zoneName => {
      writeLines(1, s"if (${genFlagName(zoneName)}) {")
      writeBody(2, zoneEdges(zoneName), doNotShadow ++ doNotDec, doNotDec)
      // val zoneGraph = buildGraph(zoneEdges(zoneName))
      // writeLines(2, zoneGraph.reorderCommands flatMap emitStmt(doNotDec))
      writeLines(1, s"}")
    }}
    // emit body (without redeclaring)
    writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
  }

  def addMemDepsToGraph(g: Graph, memUpdates: Seq[MemUpdate]) {
    // FUTURE: does not handle multiple write ports to same mem
    memUpdates foreach {
      mu => g.addNodeWithDeps(mu.memName + "$next", findDependencesMemWrite(mu))
    }
  }

  def printMuxSimilarity(bodyEdges: Seq[HyperedgeDep]) {
    val allMuxExpr = findMuxExpr(bodyEdges) map { _._2 }
    val allConds = allMuxExpr map { m: Mux => emitExpr(m.cond) }
    println(s"There are ${allMuxExpr.size} muxes in the design, with ${allConds.distinct.size} distinct conditions")
  }

  def yankRegResets(allRegDefs: Seq[DefRegister]): Seq[String] = {
    val updatesWithResets = allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
    resetGroups.toSeq flatMap {
      case (resetName, regDefs) => {
        val body = regDefs map {
          r => s"$tabs${r.name}$$next = ${emitExpr(r.init)};"
        }
        Seq(s"if ($resetName) {") ++ body ++ Seq("}")
      }
    }
  }

  def compressFlags(zoneToInputs: Map[String, Seq[String]]): Map[String,String] = {
    val allInputZonePairs = zoneToInputs flatMap {
      case (name, inputs) => inputs map { (_, name) }
    }
    val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
      case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
    }
    val allInputs = zoneToInputs.values.flatten.toSet.toSeq
    val numChecksOrig = zoneToInputs.values.flatten.size
    println(s"There are ${allInputs.size} distinct zone inputs used in $numChecksOrig checks")
    val sigToMaxIntersects = (allInputs map { sigName => {
      val childZones = inputToConsumingZones(sigName)
      val consistentCompanions = childZones map zoneToInputs map { _.toSet} reduceLeft { _.intersect(_) }
      (sigName, consistentCompanions)
    }}).toMap
    val confirmedSubsets = (allInputs groupBy sigToMaxIntersects).values filter { _.size > 1 }
    // FUTURE: think this is still leaving out a couple partial overlap subsets
    println(s"Agreed on ${confirmedSubsets.size} subsets")
    val renames = (confirmedSubsets flatMap {
      subset => subset map { sigName => (sigName, subset.head + "$shared") }
    }).toMap
    val flagsAfterCompression = (allInputs map { sigName => renames.getOrElse(sigName, sigName) }).distinct
    val numInputsAfterCompression = (zoneToInputs.values map {
      zoneInputs => (zoneInputs map { sigName => renames.getOrElse(sigName, sigName) }).distinct
    }).flatten.size
    println(s"Could be ${flagsAfterCompression.size} distinct zone flags used in $numInputsAfterCompression checks")
    // println(s"${confirmedSubsets.flatten.size} ${confirmedSubsets.flatten.toSet.size}")
    renames
  }

  def renameAndUnique(origList: Seq[String], renames: Map[String,String]) = {
    val renamed = origList map { name => renames.getOrElse(name, name) }
    renamed.distinct
  }

  def writeBodyWithZonesML(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
                           regDefs: Seq[DefRegister], resetTree: Seq[String],
                           topName: String, otherDeps: Seq[String],
                           doNotShadow: Seq[String], memUpdates: Seq[MemUpdate],
                           extIOtypes: Map[String, Type]) {
    val trackActivity = false
    val exportSparsity = false
    // map of name -> original hyperedge
    val heMap = (bodyEdges map { he => (he.name, he) }).toMap
    val regNamesSet = regNames.toSet
    // printMuxSimilarity(bodyEdges)

    // calculate zones based on all edges
    val g = buildGraph(bodyEdges)
    // val zoneMapWithSources = g.findZonesTopo3(regNames, doNotShadow)
    // val zoneMapWithSources = g.findZonesKern(regNames, doNotShadow)
    // val zoneMapWithSources = g.findZonesML(regNames, doNotShadow)
    val zoneMapWithSources = g.findZonesMFFC(doNotShadow)
    val zoneMap = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
    // g.writeZoneInfo("mffcs.zones", zoneMapWithSources)
    g.analyzeZoningQuality(zoneMap)
    // g.printDeadRegisters(regNames, otherDeps)
    val flagRenames = compressFlags(zoneMap.mapValues(_.inputs))
    val inputsToZones = zoneMap.flatMap(_._2.inputs).toSet
    val nodesInZones = zoneMap.flatMap(_._2.members).toSet
    val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
    val outputsFromZones = zoneMap.flatMap(_._2.outputs).toSet.diff(regNamesSet)

    // sparsity output
    val zoneStmtOutputOrder = scala.collection.mutable.ArrayBuffer[String]()
    if (exportSparsity) {
      g.writeCOOFile("rocketchip.coo")
      g.writeCOOFile("rocketchip.topo.coo", Option(g.reorderNames.toSeq))
    }

    // predeclare output nodes
    val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
    val outputPairs = (outputTypes zip outputsFromZones).toSeq
    val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
    writeLines(0, preDecs)
    // activity tracking
    if (trackActivity) {
      writeLines(0, "uint64_t total_transitions = 0;")
      writeLines(0, "uint64_t total_zones_active = 0;")
      writeLines(0, "uint64_t cycles_ticked = 0;")
      writeLines(0, "uint64_t outputs_checked = 0;")
      writeLines(0, "uint64_t outputs_silenced = 0;")
      // val zoneActCounts = zoneMap.keys map genFlagName map {
      //   zoneName => s"uint64_t ${zoneName}_ACTS = 0;"
      // }
      // writeLines(0, zoneActCounts.toSeq)
    }
    val doNotDec = outputsFromZones.toSet
    println(s"Output nodes: ${outputsFromZones.size}")

    // set input flags to true for other inputs (resets, mems, or external IOs)
    // FUTURE: remove. should make change detection for these inputs so consuming
    //         zones have a chance to sleep
    val otherFlags = inputsToZones diff (regNamesSet ++ zoneMapWithSources.flatMap(_._2.outputs).toSet)
    val memNames = memUpdates map { _.memName }
    val memFlags = otherFlags intersect memNames.toSet
    val memWriteTrackDecs = memFlags map {
      flagName => s"bool WTRACK_${flagName.replace('.','$')};"
    }
    writeLines(0, memWriteTrackDecs.toSeq)
    val nonMemFlags = otherFlags diff memNames.toSet
    // FUTURE: fix, can't be hacking for reset, but reset isn't in signal map table
    val nonMemFlagTypes = nonMemFlags.toSeq map {
      name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
    }
    val nonMemPreDecs = (nonMemFlagTypes zip nonMemFlags.toSeq) map {
      case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
    }
    writeLines(0, nonMemPreDecs)

    writeLines(0, s"bool sim_cached = false;")

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, resetTree)
    // predeclare zone activity flags
    val nonRegActSigs = (inputsToZones diff regNamesSet).toSeq
    val nonRegActSigsCompressed = renameAndUnique(nonRegActSigs, flagRenames)
    val inputRegs = (regNamesSet intersect inputsToZones).toSeq
    val inputRegsCompressed = ((renameAndUnique(inputRegs, flagRenames)).toSet -- nonRegActSigsCompressed.toSet).toSeq
    val otherRegs = (regNamesSet diff inputRegs.toSet).toSeq
    println(s"Unzoned regs: ${otherRegs.size}")
    val nonRegActFlagDecs = nonRegActSigsCompressed map {
      sigName => s"bool ${genFlagName(sigName)} = !sim_cached;"
    }
    writeLines(1, nonRegActFlagDecs)
    writeLines(1, inputRegsCompressed map { regName => s"bool ${genFlagName(regName)};" })
    println(s"Activity flags: ${renameAndUnique(inputsToZones.toSeq, flagRenames).size}")
    writeLines(1, yankRegResets(regDefs))

    // emit reg updates (with update checks)
    if (!regDefs.isEmpty || trackActivity) {
      if (trackActivity) {
        // writeZoneActivityTracking(zoneMap.keys.toSeq)
        writeLines(1, s"const uint64_t num_zones = ${zoneMap.size};")
        writeLines(1, s"uint64_t zones_active = 0;")
      }
      // intermixed
      writeLines(1, "if (update_registers && sim_cached) {")
      if (trackActivity) {
        writeRegActivityTracking(regNames)
      }
      val checkAndUpdates = inputRegs flatMap {
        regName => Seq(s"${genFlagName(regName, flagRenames)} |= $regName != $regName$$next;",
                       s"$regName = $regName$$next;")
      }
      writeLines(2, checkAndUpdates)
      writeLines(2, otherRegs map { regName => s"$regName = $regName$$next;"})
      // writeLines(2, regDefs map emitRegUpdate)
      writeLines(1, "} else if (update_registers) {")
      writeLines(2, regNames map { regName => s"$regName = $regName$$next;"})
      writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} = true;"})
      writeLines(1, "} else if (sim_cached) {")
      // FUTURE: for safety, should this be regNames (instead of inputRegs)
      writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} |= false;"})
      writeLines(1, "}")
    }
    writeLines(1, "sim_cached = !reset;")

    // set input flags to true for mem inputs
    // FUTURE: if using mem name for hashing, what if multiple write ports?
    val memEnablesAndMasks = (memUpdates map {
      mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
    }).toMap
    val memFlagsTrue = memFlags map {
      flagName => s"${genFlagName(flagName, flagRenames)} = true;"
    }
    val memChangeDetects = memFlags map { flagName => {
      val trackerName = s"WTRACK_${flagName.replace('.','$')}"
      s"${genFlagName(flagName, flagRenames)} |= $trackerName;"
    }}
    writeLines(1, memChangeDetects.toSeq)

    // do activity detection on other inputs (external IOs and resets)
    val nonMemChangeDetects = nonMemFlags map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      val flagName = genFlagName(sigName, flagRenames)
      s"$flagName |= $sigName != $oldVersion;"
    }}
    writeLines(1, nonMemChangeDetects.toSeq)
    // cache old versions
    val nonMemCaches = nonMemFlags map { sigName => {
      val oldVersion = s"${sigName.replace('.','$')}$$old"
      s"$oldVersion = $sigName;"
    }}
    writeLines(1, nonMemCaches.toSeq)
    // val zoneDescendants = findZoneDescendants(memFlags.toSet, zoneMap)
    // println(s"Descended from true flags: ${zoneDescendants.size}")

    // compute zone order
    // map of name -> zone name (if in zone)
    val nameToZoneName = zoneMap flatMap {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
        outputs map { portName => (portName, zoneName) }
    }}
    // list of super hyperedges for zones
    val zoneSuperEdges = zoneMap map {
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
    // gTopLevel.writeDotFile("zonegraph.dot")

    // emit zone of sources
    if (zoneMapWithSources.contains("ZONE_SOURCE")) {
      val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
      val sourceZoneEdges = sourceZoneInfo.members map heMap
      writeBody(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
      if (exportSparsity) zoneStmtOutputOrder ++= buildGraph(sourceZoneEdges.toSeq).reorderNames
    }

    // stash of ability to do get register depths
    // addMemDepsToGraph(g, memUpdates)
    // val stateDepths = g.findStateDepths(regNames ++ memNames, extIOtypes.keys.toSeq)

    // emit each zone
    // zonesReordered map zoneMap foreach { case Graph.ZoneInfo(inputs, members, outputs) => {
    zonesReordered map { zoneName => (zoneName, zoneMap(zoneName)) } foreach {
        case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
      val sensitivityListStr = renameAndUnique(inputs, flagRenames) map genFlagName mkString(" || ")
      if (sensitivityListStr.isEmpty)
        writeLines(1, s"{")
      else
        writeLines(1, s"if ($sensitivityListStr) {")
      if (trackActivity) {
        writeLines(2, "zones_active++;")
        // writeLines(2, s"${genFlagName(zoneName)}_ACTS++;")
      }
      val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
      val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
      val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
        s"${genCppType(tpe)} $name$$old = $name;"
      }}
      writeLines(2, oldOutputs)
      val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
      writeBody(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
      if (trackActivity) {
        writeLines(2, s"outputs_checked += ${outputsCleaned.size};")
        val outputsSilenced = outputsCleaned map {
          name => s"if ($name == $name$$old) outputs_silenced++;"
        }
        writeLines(2, outputsSilenced)
      }
      val outputChangeDetections = outputsCleaned map {
        name => s"${genFlagName(name, flagRenames)} |= $name != $name$$old;"
      }
      writeLines(2, outputChangeDetections)
      writeLines(1, "}")
      if (exportSparsity) zoneStmtOutputOrder ++= buildGraph(zoneEdges.toSeq).reorderNames
    }}

    if (trackActivity) {
      writeLines(2, s"total_zones_active += zones_active;")
      writeLines(2, s"""printf("Zones Active %llu/%llu\\n", zones_active, num_zones);""")
      writeLines(2, s"""printf("Average Zones: %g\\n", (double) total_zones_active/cycles_ticked);""")
      writeLines(2, s"""printf("Outputs Silenced: %llu/%llu\\n", outputs_silenced, outputs_checked);""")
    }

    // emit rest of body (without redeclaring)
    writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
    if (exportSparsity) {
      zoneStmtOutputOrder ++= buildGraph(nonZoneEdges.toSeq).reorderNames
      g.writeCOOFile("rocketchip.zones.coo", Option(zoneStmtOutputOrder.toSeq))
    }

    // printZoneStateAffinity(zoneMapWithSources, regNames, memUpdates)

    val memWriteTrackerUpdates = memFlags map { flagName => {
      val trackerName = s"WTRACK_${flagName.replace('.','$')}"
      val condition = memEnablesAndMasks(flagName).mkString(" && ");
      s"$trackerName = $condition;"
    }}
    writeLines(1, memWriteTrackerUpdates.toSeq)

    // if (trackActivity) {
    //   writeLines(1, "if (ZONE_SimDTM_1$exit) {")
    //   val zoneActCountsPrints = zoneMap.keys map genFlagName map {
    //     zoneName => s"""printf("${zoneName}: %llu\\n", ${zoneName}_ACTS);"""
    //   }
    //   writeLines(2, zoneActCountsPrints.toSeq)
    //   writeLines(1, "}")
    // }
  }

  def printZoneStateAffinity(zoneMap: Map[String,Graph.ZoneInfo],
                             regNames: Seq[String], memUpdates: Seq[MemUpdate]) {
    val regNamesSet = regNames.toSet
    val regNameZoneNamePairs = zoneMap.toSeqh flatMap {
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

  def emitEval(topName: String, circuit: Circuit) = {
    val simpleOnly = false
    val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
    val allInstances = Seq((topModule.name, "")) ++
      findAllModuleInstances("", circuit)(topModule.body)
    val module_results = allInstances map {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => emitBody(m, circuit, prefix)
        case em: ExtModule => (Seq(), EmptyStmt, Seq())
      }
    }
    val extIOs = allInstances flatMap {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => Seq()
        case em: ExtModule => { em.ports map {
          port => (s"$prefix${port.name}", port.tpe)
        }}
      }
    }
    val resetTree = buildResetTree(allInstances)
    val (allRegDefs, allBodies, allMemUpdates) = module_results.unzip3
    val allDeps = allBodies flatMap findDependencesStmt
    val (otherDeps, prints, stops) = separatePrintsAndStops(allDeps)
    val regNames = allRegDefs.flatten map { _.name }
    val memDeps = (allMemUpdates.flatten) flatMap findDependencesMemWrite
    val pAndSDeps = (prints ++ stops) flatMap { he => he.deps }
    writeLines(0, "")
    // decRegActivityTracking(regNames)
    // writeLines(0, "")
    if (simpleOnly) {
      writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
      writeLines(1, resetTree)
      // emit reg updates
      if (!allRegDefs.isEmpty) {
        writeLines(1, "if (update_registers) {")
        // recRegActivityTracking(regNames)
        writeLines(2, allRegDefs.flatten map emitRegUpdate)
        writeLines(1, "}")
      }
      writeBodySimple(1, otherDeps, regNames)
      // writeBody(1, otherDeps, (regNames ++ memDeps ++ pAndSDeps).distinct, regNames.toSet)
    } else {
      writeBodyWithZonesML(otherDeps, regNames, allRegDefs.flatten, resetTree,
                           topName, memDeps ++ pAndSDeps, (regNames ++ memDeps ++ pAndSDeps).distinct,
                           allMemUpdates.flatten, extIOs.toMap)
    }
    if (!prints.isEmpty || !stops.isEmpty) {
      writeLines(1, "if (done_reset && update_registers) {")
      if (!prints.isEmpty) {
        writeLines(2, "if(verbose) {")
        writeLines(3, (prints map {dep => dep.stmt} flatMap emitStmt(Set())))
        writeLines(2, "}")
      }
      writeLines(2, (stops map {dep => dep.stmt} flatMap emitStmt(Set())))
      writeLines(1, "}")
    }
    writeLines(1, allMemUpdates.flatten map emitMemUpdate)
    writeLines(0, "}")
    writeLines(0, "")
    // printRegActivityTracking(regNames)
  }


  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
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
    writeLines(0, s"void $topName::connect_harness(CommWrapper<struct $topName> *comm) {")
    writeLines(1, HarnessGenerator.harnessConnections(topModule))
    writeLines(0, "}")
    writeLines(0, "")
    emitEval(topName, circuit)
    writeLines(0, s"#endif  // $headerGuardName")
    TransformResult(circuit)
  }
}



// Copied from firrtl.EmitVerilogFromLowFirrtl
class FinalCleanups extends Transform with SimpleRun {
  val passSeq = Seq(
    firrtl.passes.RemoveValidIf,
    firrtl.passes.ConstProp,
    firrtl.passes.PadWidths,
    firrtl.passes.ConstProp,
    firrtl.passes.Legalize,
    firrtl.passes.VerilogWrap,
    firrtl.passes.memlib.VerilogMemDelays,
    firrtl.passes.ConstProp,
    firrtl.passes.SplitExpressions,
    firrtl.passes.CommonSubexpressionElimination,
    firrtl.passes.DeadCodeElimination,
    firrtl.passes.RemoveEmpty,
    essent.passes.InferAddw,
    essent.passes.WireConstProp,
    essent.passes.ZeroFromBits,
    essent.passes.WireConstProp,
    essent.passes.RandInitInvalids,
    essent.passes.NoResetsOrClockConnects,
    essent.passes.RegFromMem1)
    // passes.VerilogRename,
    // passes.VerilogPrep)
  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    run(circuit, passSeq)
  }
}

class PrintCircuit extends Transform with SimpleRun {
  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    println(circuit.serialize)
    TransformResult(circuit)
  }
}



class CCCompiler(verbose: Boolean) extends Compiler {
  def transforms(writer: Writer): Seq[Transform] = Seq(
    new firrtl.Chisel3ToHighFirrtl,
    new firrtl.IRToWorkingIR,
    new firrtl.ResolveAndCheck,
    new firrtl.HighFirrtlToMiddleFirrtl,
    new firrtl.passes.memlib.InferReadWrite(TransID(-1)),
    new firrtl.passes.memlib.ReplSeqMem(TransID(-2)),
    new firrtl.MiddleFirrtlToLowFirrtl,
    new firrtl.passes.InlineInstances(TransID(0)),
    new FinalCleanups,
    new EmitCpp(writer)
  ) ++ (if (verbose) Seq(new PrintCircuit) else Seq())
}
