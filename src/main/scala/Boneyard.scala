// Unused code that should soon be deleted


// from Compiler.scala

// def writeBody(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], doNotShadow: Seq[String],
//     doNotDec: Set[String]) {
//   if (!bodyEdges.isEmpty) {
//     // val muxOutputNames = findMuxOutputNames(bodyEdges)
//     // name to mux expression
//     val muxMap = findMuxExpr(bodyEdges).toMap
//     val shadows = buildGraph(bodyEdges).findAllShadows(muxMap, doNotShadow)
//     // map of muxName -> true shadows, map of muxName -> false shadows
//     val trueShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, tShadow)}).toMap
//     val falseShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, fShadow)}).toMap
//     // set of signals in shadows
//     val shadowedSigs = (shadows flatMap {
//       case (muxName, tShadow, fShadow) => (tShadow ++ fShadow) }).toSet
//     if (indentLevel == 1) println(s"Total shadow size: ${shadowedSigs.size}")
//     // map of name -> original hyperedge
//     val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//     // top level edges (filter out shadows) & make muxes depend on shadow inputs
//     val unshadowedHE = bodyEdges filter {he => !shadowedSigs.contains(he.name)}
//     val topLevelHE = unshadowedHE map { he => {
//       val deps = if (!trueShadows.contains(he.name)) he.deps
//                  else {
//                    val shadowDeps = (trueShadows(he.name) ++ falseShadows(he.name)) flatMap { heMap(_).deps }
//                    he.deps ++ shadowDeps
//                  }
//       // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
//       HyperedgeDep(he.name, deps.distinct, he.stmt)
//     }}
//     // build graph on new hyperedges and run topo sort
//     val reorderedNames = buildGraph(topLevelHE).reorderNames
//     reorderedNames foreach { name => {
//       val stmt = heMap(name).stmt
//       if ((trueShadows.contains(name)) && ((!trueShadows(name).isEmpty) || (!falseShadows(name).isEmpty))) {
//         val muxExpr = muxMap(name)
//         // declare output type
//         val resultTpe = findResultType(stmt)
//         if ((!name.endsWith("$next")) && (!doNotDec.contains(name)))
//           writeLines(indentLevel, s"${genCppType(resultTpe)} $name;")
//         writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
//         val trueHE = trueShadows(name) map { heMap(_) }
//         writeBody(indentLevel + 1, trueHE, doNotShadow, doNotDec)
//         writeLines(indentLevel + 1, s"$name = ${emitExpr(muxExpr.tval)};")
//         writeLines(indentLevel, "} else {")
//         val falseHE = falseShadows(name) map { heMap(_) }
//         writeBody(indentLevel + 1, falseHE, doNotShadow, doNotDec)
//         writeLines(indentLevel + 1, s"$name = ${emitExpr(muxExpr.fval)};")
//         writeLines(indentLevel, "}")
//       } else writeLines(indentLevel, emitStmt(doNotDec)(stmt))
//     }}
//   }
// }

// def writeBodyWithZones(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
//                        allRegUpdates: Seq[String], resetTree: Seq[String],
//                        topName: String, otherDeps: Seq[String],
//                        doNotShadow: Seq[String]) {
//   val trackActivity = false
//   // map of name -> original hyperedge
//   val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//   // calculate zones based on all edges
//   val allZones = buildGraph(bodyEdges).findZones(regNames)
//   val zoneMap = allZones filter { case (k,v) => v.size > 10}
//   // set of all nodes in zones
//   val nodesInZones = zoneMap.values.flatten.toSet
//   println(s"Nodes in zones: ${nodesInZones.size}")
//   // map of zone name -> zone edges (easy) - needed?
//   val zoneEdges = zoneMap map {case (k,v) => (k, v filter {heMap.contains} map {heMap})}
//   // seq of edges not in zones
//   val nonZoneEdges = bodyEdges filter { he => !nodesInZones.contains(he.name) }
//   // set of all dependences from non-zone edges
//   val nonZoneDeps = (nonZoneEdges map { _.deps }).flatten.toSet ++ otherDeps.toSet
//   // output nodes (intersection of deps and zone nodes)
//   val zoneOutputs = nonZoneDeps.intersect(nodesInZones) filter {!regNames.contains(_)}
//   val doNotDec = zoneOutputs.toSet
//   // predeclare output nodes
//   val outputTypes = zoneOutputs.toSeq map {name => findResultType(heMap(name).stmt)}
//   val outputPairs = (outputTypes zip zoneOutputs).toSeq
//   val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
//   writeLines(0, preDecs)
//   // activity tracking
//   if (trackActivity) {
//     writeLines(0, "uint64_t total_transitions = 0;")
//     writeLines(0, "uint64_t total_zones_active = 0;")
//     writeLines(0, "uint64_t cycles_ticked = 0;")
//   }
//   // start emitting eval function
//   writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
//   writeLines(1, resetTree)
//   // predeclare zone activity flags
//   writeLines(1, (zoneMap.keys map { zoneName => s"bool ${genFlagName(zoneName)} = reset;"}).toSeq)
//   // emit update checks
//   zoneMap foreach { case (zoneName, zoneContents) => {
//     writeLines(1, s"if ($zoneName != $zoneName$$next) ${genFlagName(zoneName)} = true;")
//     zoneContents filter { name => regNames.contains(name) } foreach { name =>
//       writeLines(1, s"if ($name != $name$$next) ${genFlagName(zoneName)} = true;")}
//   }}
//   // emit reg updates
//   if (!allRegUpdates.isEmpty || trackActivity) {
//     writeLines(1, "if (update_registers) {")
//     if (trackActivity) {
//       writeRegActivityTracking(regNames)
//       writeZoneActivityTracking(zoneMap.keys.toSeq)
//     }
//     writeLines(2, allRegUpdates)
//     writeLines(1, "}")
//   }
//   // emit each zone
//   zoneMap.keys foreach { zoneName => {
//     writeLines(1, s"if (${genFlagName(zoneName)}) {")
//     writeBody(2, zoneEdges(zoneName), doNotShadow ++ doNotDec, doNotDec)
//     // val zoneGraph = buildGraph(zoneEdges(zoneName))
//     // writeLines(2, zoneGraph.reorderCommands flatMap emitStmt(doNotDec))
//     writeLines(1, s"}")
//   }}
//   // emit body (without redeclaring)
//   writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
// }



// def compressFlags(zoneToInputs: Map[String, Seq[String]]): Map[String,String] = {
//   val allInputZonePairs = zoneToInputs flatMap {
//     case (name, inputs) => inputs map { (_, name) }
//   }
//   val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
//     case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
//   }
//   val allInputs = zoneToInputs.values.flatten.toSet.toSeq
//   val numChecksOrig = zoneToInputs.values.flatten.size
//   println(s"There are ${allInputs.size} distinct zone inputs used in $numChecksOrig checks")
//   val sigToMaxIntersects = (allInputs map { sigName => {
//     val childZones = inputToConsumingZones(sigName)
//     val consistentCompanions = childZones map zoneToInputs map { _.toSet} reduceLeft { _.intersect(_) }
//     (sigName, consistentCompanions)
//   }}).toMap
//   val confirmedSubsets = (allInputs groupBy sigToMaxIntersects).values filter { _.size > 1 }
//   // FUTURE: think this is still leaving out a couple partial overlap subsets
//   println(s"Agreed on ${confirmedSubsets.size} subsets")
//   val renames = (confirmedSubsets flatMap {
//     subset => subset map { sigName => (sigName, subset.head + "$shared") }
//   }).toMap
//   val flagsAfterCompression = (allInputs map { sigName => renames.getOrElse(sigName, sigName) }).distinct
//   val numInputsAfterCompression = (zoneToInputs.values map {
//     zoneInputs => (zoneInputs map { sigName => renames.getOrElse(sigName, sigName) }).distinct
//   }).flatten.size
//   println(s"Could be ${flagsAfterCompression.size} distinct zone flags used in $numInputsAfterCompression checks")
//   // println(s"${confirmedSubsets.flatten.size} ${confirmedSubsets.flatten.toSet.size}")
//   renames
// }



// def renameAndUnique(origList: Seq[String], renames: Map[String,String]) = {
//   val renamed = origList map { name => renames.getOrElse(name, name) }
//   renamed.distinct
// }



// def printMuxSimilarity(bodyEdges: Seq[HyperedgeDep]) {
//   val allMuxExpr = findMuxExpr(bodyEdges) map { _._2 }
//   val allConds = allMuxExpr map { m: Mux => emitExpr(m.cond) }
//   println(s"There are ${allMuxExpr.size} muxes in the design, with ${allConds.distinct.size} distinct conditions")
// }



// def genFlagName(regName: String, renames: Map[String, String]): String = {
//   genFlagName(renames.getOrElse(regName, regName))
// }



// def yankRegResets(allRegDefs: Seq[DefRegister]): Seq[String] = {
//   val updatesWithResets = allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
//   val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
//   resetGroups.toSeq flatMap {
//     case (resetName, regDefs) => {
//       val body = regDefs map {
//         r => s"$tabs${r.name}$$next = ${emitExpr(r.init)};"
//       }
//       Seq(s"if ($resetName) {") ++ body ++ Seq("}")
//     }
//   }
// }



// def writeBodyWithZonesML(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
//                          regDefs: Seq[DefRegister], resetTree: Seq[String],
//                          topName: String, otherDeps: Seq[String],
//                          doNotShadow: Seq[String], memUpdates: Seq[MemUpdate],
//                          extIOtypes: Map[String, Type]) {
//   val trackActivity = false
//   val exportSparsity = false
//   // map of name -> original hyperedge
//   val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//   val regNamesSet = regNames.toSet
//   // printMuxSimilarity(bodyEdges)
//
//   // calculate zones based on all edges
//   val g = buildGraph(bodyEdges)
//   // val zoneMapWithSources = g.findZonesTopo3(regNames, doNotShadow)
//   // val zoneMapWithSources = g.findZonesKern(regNames, doNotShadow)
//   // val zoneMapWithSources = g.findZonesML(regNames, doNotShadow)
//   val zoneMapWithSources = g.findZonesMFFC(regNames, doNotShadow)
//   val zoneMap = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
//   // g.writeZoneInfo("mffcs.zones", zoneMapWithSources)
//   g.analyzeZoningQuality(zoneMap)
//   // g.printDeadRegisters(regNames, otherDeps)
//   val flagRenames = compressFlags(zoneMap.mapValues(_.inputs))
//   val inputsToZones = zoneMap.flatMap(_._2.inputs).toSet
//   val nodesInZones = zoneMap.flatMap(_._2.members).toSet
//   val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
//   val outputsFromZones = zoneMap.flatMap(_._2.outputs).toSet.diff(regNamesSet)
//
//   // sparsity output
//   val zoneStmtOutputOrder = scala.collection.mutable.ArrayBuffer[String]()
//   if (exportSparsity) {
//     g.writeCOOFile("rocketchip.coo")
//     g.writeCOOFile("rocketchip.topo.coo", Option(g.reorderNames.toSeq))
//   }
//
//   // predeclare output nodes
//   val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
//   val outputPairs = (outputTypes zip outputsFromZones).toSeq
//   val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
//   writeLines(0, preDecs)
//   // activity tracking
//   if (trackActivity) {
//     writeLines(0, "uint64_t total_transitions = 0;")
//     writeLines(0, "uint64_t total_zones_active = 0;")
//     writeLines(0, "uint64_t cycles_ticked = 0;")
//     writeLines(0, "uint64_t outputs_checked = 0;")
//     writeLines(0, "uint64_t outputs_silenced = 0;")
//     // val zoneActCounts = zoneMap.keys map genFlagName map {
//     //   zoneName => s"uint64_t ${zoneName}_ACTS = 0;"
//     // }
//     // writeLines(0, zoneActCounts.toSeq)
//   }
//   val doNotDec = outputsFromZones.toSet
//   println(s"Output nodes: ${outputsFromZones.size}")
//
//   // set input flags to true for other inputs (resets, mems, or external IOs)
//   // FUTURE: remove. should make change detection for these inputs so consuming
//   //         zones have a chance to sleep
//   val otherFlags = inputsToZones diff (regNamesSet ++ zoneMapWithSources.flatMap(_._2.outputs).toSet)
//   val memNames = memUpdates map { _.memName }
//   val memFlags = otherFlags intersect memNames.toSet
//   val memWriteTrackDecs = memFlags map {
//     flagName => s"bool WTRACK_${flagName.replace('.','$')};"
//   }
//   writeLines(0, memWriteTrackDecs.toSeq)
//   val nonMemFlags = otherFlags diff memNames.toSet
//   // FUTURE: fix, can't be hacking for reset, but reset isn't in signal map table
//   val nonMemFlagTypes = nonMemFlags.toSeq map {
//     name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
//   }
//   val nonMemPreDecs = (nonMemFlagTypes zip nonMemFlags.toSeq) map {
//     case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
//   }
//   writeLines(0, nonMemPreDecs)
//
//   writeLines(0, s"bool sim_cached = false;")
//
//   // start emitting eval function
//   writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
//   writeLines(1, resetTree)
//   // predeclare zone activity flags
//   val nonRegActSigs = (inputsToZones diff regNamesSet).toSeq
//   val nonRegActSigsCompressed = renameAndUnique(nonRegActSigs, flagRenames)
//   val inputRegs = (regNamesSet intersect inputsToZones).toSeq
//   val inputRegsCompressed = ((renameAndUnique(inputRegs, flagRenames)).toSet -- nonRegActSigsCompressed.toSet).toSeq
//   val otherRegs = (regNamesSet diff inputRegs.toSet).toSeq
//   println(s"Unzoned regs: ${otherRegs.size}")
//   val nonRegActFlagDecs = nonRegActSigsCompressed map {
//     sigName => s"bool ${genFlagName(sigName)} = !sim_cached;"
//   }
//   writeLines(1, nonRegActFlagDecs)
//   writeLines(1, inputRegsCompressed map { regName => s"bool ${genFlagName(regName)};" })
//   println(s"Activity flags: ${renameAndUnique(inputsToZones.toSeq, flagRenames).size}")
//   writeLines(1, yankRegResets(regDefs))
//
//   // emit reg updates (with update checks)
//   if (!regDefs.isEmpty || trackActivity) {
//     if (trackActivity) {
//       // writeZoneActivityTracking(zoneMap.keys.toSeq)
//       writeLines(1, s"const uint64_t num_zones = ${zoneMap.size};")
//       writeLines(1, s"uint64_t zones_active = 0;")
//     }
//     // intermixed
//     writeLines(1, "if (update_registers && sim_cached) {")
//     if (trackActivity) {
//       writeRegActivityTracking(regNames)
//     }
//     val checkAndUpdates = inputRegs flatMap {
//       regName => Seq(s"${genFlagName(regName, flagRenames)} |= $regName != $regName$$next;",
//                      s"$regName = $regName$$next;")
//     }
//     writeLines(2, checkAndUpdates)
//     writeLines(2, otherRegs map { regName => s"$regName = $regName$$next;"})
//     // writeLines(2, regDefs map emitRegUpdate)
//     writeLines(1, "} else if (update_registers) {")
//     writeLines(2, regNames map { regName => s"$regName = $regName$$next;"})
//     writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} = true;"})
//     writeLines(1, "} else if (sim_cached) {")
//     // FUTURE: for safety, should this be regNames (instead of inputRegs)
//     writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} |= false;"})
//     writeLines(1, "}")
//   }
//   writeLines(1, "sim_cached = !reset;")
//
//   // set input flags to true for mem inputs
//   // FUTURE: if using mem name for hashing, what if multiple write ports?
//   val memEnablesAndMasks = (memUpdates map {
//     mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
//   }).toMap
//   val memFlagsTrue = memFlags map {
//     flagName => s"${genFlagName(flagName, flagRenames)} = true;"
//   }
//   val memChangeDetects = memFlags map { flagName => {
//     val trackerName = s"WTRACK_${flagName.replace('.','$')}"
//     s"${genFlagName(flagName, flagRenames)} |= $trackerName;"
//   }}
//   writeLines(1, memChangeDetects.toSeq)
//
//   // do activity detection on other inputs (external IOs and resets)
//   val nonMemChangeDetects = nonMemFlags map { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     val flagName = genFlagName(sigName, flagRenames)
//     s"$flagName |= $sigName != $oldVersion;"
//   }}
//   writeLines(1, nonMemChangeDetects.toSeq)
//   // cache old versions
//   val nonMemCaches = nonMemFlags map { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     s"$oldVersion = $sigName;"
//   }}
//   writeLines(1, nonMemCaches.toSeq)
//   // val zoneDescendants = findZoneDescendants(memFlags.toSet, zoneMap)
//   // println(s"Descended from true flags: ${zoneDescendants.size}")
//
//   // compute zone order
//   // map of name -> zone name (if in zone)
//   val nameToZoneName = zoneMap flatMap {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       outputs map { portName => (portName, zoneName) }
//   }}
//   // list of super hyperedges for zones
//   val zoneSuperEdges = zoneMap map {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       HyperedgeDep(zoneName, inputs, heMap(members.head).stmt)
//   }}
//   // list of non-zone hyperedges
//   val nonZoneEdges = bodyEdges filter { he => !nodesInZonesWithSources.contains(he.name) }
//   // list of hyperedges with zone members replaced with zone names
//   val topLevelHE = zoneSuperEdges map { he:HyperedgeDep => {
//     val depsRenamedForZones = (he.deps map {
//       depName => nameToZoneName.getOrElse(depName, depName)
//     }).distinct
//     HyperedgeDep(he.name, depsRenamedForZones, he.stmt)
//   }}
//   // reordered names
//   val gTopLevel = buildGraph(topLevelHE.toSeq)
//   val zonesReordered = gTopLevel.reorderNames
//   // gTopLevel.writeDotFile("zonegraph.dot")
//
//   // emit zone of sources
//   if (zoneMapWithSources.contains("ZONE_SOURCE")) {
//     val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
//     val sourceZoneEdges = sourceZoneInfo.members map heMap
//     writeBody(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
//     if (exportSparsity) zoneStmtOutputOrder ++= buildGraph(sourceZoneEdges.toSeq).reorderNames
//   }
//
//   // stash of ability to do get register depths
//   // addMemDepsToGraph(g, memUpdates)
//   // val stateDepths = g.findStateDepths(regNames ++ memNames, extIOtypes.keys.toSeq)
//
//   // emit each zone
//   // zonesReordered map zoneMap foreach { case Graph.ZoneInfo(inputs, members, outputs) => {
//   zonesReordered map { zoneName => (zoneName, zoneMap(zoneName)) } foreach {
//       case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//     val sensitivityListStr = renameAndUnique(inputs, flagRenames) map genFlagName mkString(" || ")
//     if (sensitivityListStr.isEmpty)
//       writeLines(1, s"{")
//     else
//       writeLines(1, s"if ($sensitivityListStr) {")
//     if (trackActivity) {
//       writeLines(2, "zones_active++;")
//       // writeLines(2, s"${genFlagName(zoneName)}_ACTS++;")
//     }
//     val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
//     val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
//     val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
//       s"${genCppType(tpe)} $name$$old = $name;"
//     }}
//     writeLines(2, oldOutputs)
//     val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
//     writeBody(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
//     if (trackActivity) {
//       writeLines(2, s"outputs_checked += ${outputsCleaned.size};")
//       val outputsSilenced = outputsCleaned map {
//         name => s"if ($name == $name$$old) outputs_silenced++;"
//       }
//       writeLines(2, outputsSilenced)
//     }
//     val outputChangeDetections = outputsCleaned map {
//       name => s"${genFlagName(name, flagRenames)} |= $name != $name$$old;"
//     }
//     writeLines(2, outputChangeDetections)
//     writeLines(1, "}")
//     if (exportSparsity) zoneStmtOutputOrder ++= buildGraph(zoneEdges.toSeq).reorderNames
//   }}
//
//   if (trackActivity) {
//     writeLines(2, s"total_zones_active += zones_active;")
//     writeLines(2, s"""printf("Zones Active %llu/%llu\\n", zones_active, num_zones);""")
//     writeLines(2, s"""printf("Average Zones: %g\\n", (double) total_zones_active/cycles_ticked);""")
//     writeLines(2, s"""printf("Outputs Silenced: %llu/%llu\\n", outputs_silenced, outputs_checked);""")
//   }
//
//   // emit rest of body (without redeclaring)
//   writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
//   if (exportSparsity) {
//     zoneStmtOutputOrder ++= buildGraph(nonZoneEdges.toSeq).reorderNames
//     g.writeCOOFile("rocketchip.zones.coo", Option(zoneStmtOutputOrder.toSeq))
//   }
//
//   // printZoneStateAffinity(zoneMapWithSources, regNames, memUpdates)
//
//   val memWriteTrackerUpdates = memFlags map { flagName => {
//     val trackerName = s"WTRACK_${flagName.replace('.','$')}"
//     val condition = memEnablesAndMasks(flagName).mkString(" && ");
//     s"$trackerName = $condition;"
//   }}
//   writeLines(1, memWriteTrackerUpdates.toSeq)
//
//   // if (trackActivity) {
//   //   writeLines(1, "if (ZONE_SimDTM_1$exit) {")
//   //   val zoneActCountsPrints = zoneMap.keys map genFlagName map {
//   //     zoneName => s"""printf("${zoneName}: %llu\\n", ${zoneName}_ACTS);"""
//   //   }
//   //   writeLines(2, zoneActCountsPrints.toSeq)
//   //   writeLines(1, "}")
//   // }
// }



// def emitEval(topName: String, circuit: Circuit) = {
//   val simpleOnly = false
//   val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
//   val allInstances = Seq((topModule.name, "")) ++
//     findAllModuleInstances("", circuit)(topModule.body)
//   val module_results = allInstances map {
//     case (modName, prefix) => findModule(modName, circuit) match {
//       case m: Module => emitBody(m, circuit, prefix)
//       case em: ExtModule => (Seq(), EmptyStmt, Seq())
//     }
//   }
//   val extIOs = allInstances flatMap {
//     case (modName, prefix) => findModule(modName, circuit) match {
//       case m: Module => Seq()
//       case em: ExtModule => { em.ports map {
//         port => (s"$prefix${port.name}", port.tpe)
//       }}
//     }
//   }
//   val resetTree = buildResetTree(allInstances, circuit)
//   val (allRegDefs, allBodies, allMemUpdates) = module_results.unzip3
//   val allDeps = allBodies flatMap findDependencesStmt
//   val (otherDeps, prints, stops) = separatePrintsAndStops(allDeps)
//   val regNames = allRegDefs.flatten map { _.name }
//   val memDeps = (allMemUpdates.flatten) flatMap findDependencesMemWrite
//   val pAndSDeps = (prints ++ stops) flatMap { he => he.deps }
//   writeLines(0, "")
//   // decRegActivityTracking(regNames)
//   // writeLines(0, "")
//   if (simpleOnly) {
//     writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
//     writeLines(1, resetTree)
//     // emit reg updates
//     if (!allRegDefs.isEmpty) {
//       writeLines(1, "if (update_registers) {")
//       // recRegActivityTracking(regNames)
//       writeLines(2, allRegDefs.flatten map emitRegUpdate)
//       writeLines(1, "}")
//     }
//     writeBodySimple(1, otherDeps, regNames)
//     // writeBody(1, otherDeps, (regNames ++ memDeps ++ pAndSDeps).distinct, regNames.toSet)
//   } else {
//     writeBodyWithZonesML(otherDeps, regNames, allRegDefs.flatten, resetTree,
//                          topName, memDeps ++ pAndSDeps, (regNames ++ memDeps ++ pAndSDeps).distinct,
//                          allMemUpdates.flatten, extIOs.toMap)
//   }
//   if (!prints.isEmpty || !stops.isEmpty) {
//     writeLines(1, "if (done_reset && update_registers) {")
//     if (!prints.isEmpty) {
//       writeLines(2, "if(verbose) {")
//       writeLines(3, (prints map {dep => dep.stmt} flatMap emitStmt(Set())))
//       writeLines(2, "}")
//     }
//     writeLines(2, (stops map {dep => dep.stmt} flatMap emitStmt(Set())))
//     writeLines(1, "}")
//   }
//   writeLines(1, allMemUpdates.flatten map emitMemUpdate)
//   writeLines(0, "}")
//   writeLines(0, "")
//   // printRegActivityTracking(regNames)
// }



// def writeBodyWithZonesMLTail(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
//                          regDefs: Seq[DefRegister], resetTree: Seq[String],
//                          topName: String, otherDeps: Seq[String],
//                          doNotShadow: Seq[String], memUpdates: Seq[MemUpdate],
//                          extIOtypes: Map[String, Type]): Seq[String] = {
//   // map of name -> original hyperedge
//   val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//   val regNamesSet = regNames.toSet
//   // calculate zones based on all edges
//   val g = buildGraph(bodyEdges)
//   val zoneMapWithSources = g.findZonesMFFC(regNames, doNotShadow)
//   // val zoneMapWithSources = Map[String, Graph.ZoneInfo]()
//   val zoneMap = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
//   g.analyzeZoningQuality(zoneMap)
//   val flagRenames = compressFlags(zoneMap.mapValues(_.inputs))
//   val inputsToZones = zoneMap.flatMap(_._2.inputs).toSet
//   val nodesInZones = zoneMap.flatMap(_._2.members).toSet
//   val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
//   val outputsFromZones = zoneMap.flatMap(_._2.outputs).toSet.diff(regNamesSet)
//
//   // predeclare output nodes
//   val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
//   val outputPairs = (outputTypes zip outputsFromZones).toSeq
//   // val noPermSigs = outputPairs filter { !_._2.contains('.') }
//   val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
//   writeLines(0, preDecs)
//
//   val doNotDec = outputsFromZones.toSet
//   println(s"Output nodes: ${outputsFromZones.size}")
//
//   // set input flags to true for other inputs (resets, mems, or external IOs)
//   // FUTURE: remove. should make change detection for these inputs so consuming
//   //         zones have a chance to sleep
//   val otherFlags = inputsToZones diff (regNamesSet ++ zoneMapWithSources.flatMap(_._2.outputs).toSet)
//   val memNames = memUpdates map { _.memName }
//   val memFlags = otherFlags intersect memNames.toSet
//   val memWriteTrackDecs = memFlags map {
//     flagName => s"bool WTRACK_${flagName.replace('.','$')};"
//   }
//   writeLines(0, memWriteTrackDecs.toSeq)
//   val nonMemFlags = otherFlags diff memNames.toSet
//   // FUTURE: fix, can't be hacking for reset, but reset isn't in signal map table
//   val nonMemFlagTypes = nonMemFlags.toSeq map {
//     name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
//   }
//   val nonMemPreDecs = (nonMemFlagTypes zip nonMemFlags.toSeq) map {
//     case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
//   }
//   writeLines(0, nonMemPreDecs)
//
//   // predeclare zone activity flags
//   val nonRegActSigs = (inputsToZones diff regNamesSet).toSeq
//   val nonRegActSigsCompressed = renameAndUnique(nonRegActSigs, flagRenames)
//   val inputRegs = (regNamesSet intersect inputsToZones).toSeq
//   val inputRegsCompressed = ((renameAndUnique(inputRegs, flagRenames)).toSet -- nonRegActSigsCompressed.toSet).toSeq
//   val regsUnreadByZones = (regNamesSet diff inputRegs.toSet).toSeq
//   println(s"Regs unread by zones: ${regsUnreadByZones.size}")
//   val regsSetInZones = (regNamesSet intersect nodesInZones).toSeq
//   val regsUnsetByZones = (regNamesSet diff inputRegs.toSet).toSeq
//   println(s"Regs unset by zones: ${regsUnsetByZones.size}")
//   val allFlags = nonRegActSigsCompressed ++ inputRegsCompressed
//   writeLines(0, allFlags map { sigName => s"bool ${genFlagName(sigName)};" })
//
//   writeLines(0, s"bool sim_cached = false;")
//   writeLines(0, s"bool regs_set = false;")
//
//   // start emitting eval function
//   writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
//   writeLines(1, resetTree)
//
//   writeLines(1, "if (!sim_cached) {")
//   writeLines(2, allFlags map { sigName => s"${genFlagName(sigName)} = true;" })
//   writeLines(1, "}")
//
//   // val nonRegActFlagDecs = nonRegActSigsCompressed map {
//   //   sigName => s"${genFlagName(sigName)} = !sim_cached;"
//   // }
//   // writeLines(1, nonRegActFlagDecs)
//   // writeLines(1, inputRegsCompressed map { regName => s"${genFlagName(regName)} = true;" })
//   println(s"Activity flags: ${renameAndUnique(inputsToZones.toSeq, flagRenames).size}")
//
//   // emit reg updates (with update checks)
//   // if (!regDefs.isEmpty) {
//     // intermixed
//     // writeLines(1, "if (update_registers && sim_cached) {")
//     // writeLines(1, "if (update_registers) {")
//     // val checkAndUpdates = inputRegs flatMap {
//     //   regName => Seq(s"${genFlagName(regName, flagRenames)} |= $regName != $regName$$next;",
//     //                  s"$regName = $regName$$next;")
//     // }
//     // writeLines(2, checkAndUpdates)
//     // writeLines(2, otherRegs map { regName => s"$regName = $regName$$next;"})
//     // // writeLines(2, regDefs map emitRegUpdate)
//     // writeLines(1, "} else if (update_registers) {")
//     // writeLines(2, regNames map { regName => s"$regName = $regName$$next;"})
//     // writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} = true;"})
//     // writeLines(1, "} else if (sim_cached) {")
//     // // FUTURE: for safety, should this be regNames (instead of inputRegs)
//     // writeLines(2, inputRegsCompressed map { regName => s"${genFlagName(regName, flagRenames)} |= false;"})
//     // writeLines(1, "}")
//   // }
//   writeLines(1, "sim_cached = regs_set;")
//
//   // set input flags to true for mem inputs
//   // FUTURE: if using mem name for hashing, what if multiple write ports?
//   val memEnablesAndMasks = (memUpdates map {
//     mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
//   }).toMap
//   val memFlagsTrue = memFlags map {
//     flagName => s"${genFlagName(flagName, flagRenames)} = true;"
//   }
//   val memChangeDetects = memFlags map { flagName => {
//     val trackerName = s"WTRACK_${flagName.replace('.','$')}"
//     s"${genFlagName(flagName, flagRenames)} |= $trackerName;"
//   }}
//   writeLines(1, memChangeDetects.toSeq)
//
//   // do activity detection on other inputs (external IOs and resets)
//   val nonMemChangeDetects = nonMemFlags map { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     val flagName = genFlagName(sigName, flagRenames)
//     s"$flagName |= $sigName != $oldVersion;"
//   }}
//   writeLines(1, nonMemChangeDetects.toSeq)
//   // cache old versions
//   val nonMemCaches = nonMemFlags map { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     s"$oldVersion = $sigName;"
//   }}
//   writeLines(1, nonMemCaches.toSeq)
//
//   // compute zone order
//   // map of name -> zone name (if in zone)
//   val nameToZoneName = zoneMap flatMap {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       outputs map { portName => (portName, zoneName) }
//   }}
//   // list of super hyperedges for zones
//   val zoneSuperEdges = zoneMap map {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       HyperedgeDep(zoneName, inputs, heMap(members.head).stmt)
//   }}
//   // list of non-zone hyperedges
//   val nonZoneEdges = bodyEdges filter { he => !nodesInZonesWithSources.contains(he.name) }
//   // list of hyperedges with zone members replaced with zone names
//   val topLevelHE = zoneSuperEdges map { he:HyperedgeDep => {
//     val depsRenamedForZones = (he.deps map {
//       depName => nameToZoneName.getOrElse(depName, depName)
//     }).distinct
//     HyperedgeDep(he.name, depsRenamedForZones, he.stmt)
//   }}
//   // reordered names
//   val gTopLevel = buildGraph(topLevelHE.toSeq)
//   val zonesReordered = gTopLevel.reorderNames
//
//   // determine last use of flags
//   val flagNameZoneNameTuples = zonesReordered flatMap { zoneName => {
//     val rawInputs = zoneMap(zoneName).inputs
//     val flagsUsed = renameAndUnique(rawInputs, flagRenames)
//     flagsUsed map { (_, zoneName) }
//   }}
//   val flagToConsumingZones = flagNameZoneNameTuples groupBy { _._1 } mapValues { _ map {_._2} }
//   val flagToLastZone = flagToConsumingZones map {
//     case (flagName, consumingZones) => (flagName, consumingZones.last)
//   }
//   val zoneToLastFlags = flagToLastZone.keys groupBy { flagToLastZone(_) }
//
//   // emit zone of sources
//   if (zoneMapWithSources.contains("ZONE_SOURCE")) {
//     val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
//     val sourceZoneEdges = sourceZoneInfo.members map heMap
//     // FUTURE: does this need to be made into tail?
//     writeBody(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
//   }
//
//   // emit each zone
//   zonesReordered map { zoneName => (zoneName, zoneMap(zoneName)) } foreach {
//       case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//     val sensitivityListStr = renameAndUnique(inputs, flagRenames) map genFlagName mkString(" || ")
//     if (sensitivityListStr.isEmpty)
//       writeLines(1, s"{")
//     else
//       writeLines(1, s"if ($sensitivityListStr) {")
//     val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
//     val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
//     val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
//       s"${genCppType(tpe)} $name$$old = $name;"
//     }}
//     writeLines(2, oldOutputs)
//     val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
//     // FUTURE: shouldn't this be made into tail?
//     writeBody(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
//     val flagOffs = (zoneToLastFlags.getOrElse(zoneName, Seq()) map {
//       flagName => s"${genFlagName(flagName, flagRenames)} = false;"
//     }).toSeq
//     writeLines(2, flagOffs)
//     val outputChangeDetections = outputsCleaned map {
//       name => s"${genFlagName(name, flagRenames)} |= $name != $name$$old;"
//     }
//     writeLines(2, outputChangeDetections)
//     writeLines(1, "}")
//   }}
//
//   // emit rest of body (without redeclaring)
//   // FUTURE: does this need to be made into tail?
//   writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
//
//   val memWriteTrackerUpdates = memFlags map { flagName => {
//     val trackerName = s"WTRACK_${flagName.replace('.','$')}"
//     val condition = memEnablesAndMasks(flagName).mkString(" && ");
//     s"$trackerName = $condition;"
//   }}
//   writeLines(1, memWriteTrackerUpdates.toSeq)
//
//   // init flags (and then start filling)
//   // writeLines(1, allFlags map { sigName => s"${genFlagName(sigName)} = false;" })
//   val regChecks = inputRegs map {
//     regName => s"${genFlagName(regName, flagRenames)} |= $regName != $regName$$next;"
//   }
//   writeLines(1, regChecks)
//   Seq()
// }

// Emitter that performs single-phase reg updates (merges) when possible, and returns merged regs
// def writeBodyRegTailOpt(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], regNames: Seq[String]): Seq[String] = {
//   val nameToStmt = (bodyEdges map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
//   val g = buildGraph(bodyEdges)
//   val mergedRegs = g.mergeRegsSafe(regNames)
//   val mergedRegWrites = (mergedRegs map { _ + "$next" }).toSet
//   g.reorderNames foreach { name => {
//     if (mergedRegWrites.contains(name)) {
//       val emitted = emitStmt(Set())(nameToStmt(name)).head
//       val replaced = emitted.replaceAllLiterally("$next", "")
//       writeLines(indentLevel, "if (update_registers) " + replaced)
//     } else {
//       writeLines(indentLevel, emitStmt(Set())(nameToStmt(name)))
//     }
//   }}
//   mergedRegs
// }

// Emitter that shadows muxes in addition to single-phase reg updates
// def writeBodyMuxOpt(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], doNotShadow: Seq[String],
//     doNotDec: Set[String], regsToConsider: Seq[String]=Seq()): Seq[String] = {
//   if (bodyEdges.nonEmpty) {
//     // name to mux expression
//     val muxMap = findMuxExpr(bodyEdges).toMap
//     val shadows = buildGraph(bodyEdges).findAllShadows(muxMap, doNotShadow)
//     // map of muxName -> true shadows, map of muxName -> false shadows
//     val trueShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, tShadow)}).toMap
//     val falseShadows = (shadows map {case (muxName, tShadow, fShadow) => (muxName, fShadow)}).toMap
//     // only shadow mux if stuff on at least one side
//     val shadowedMuxes = (muxMap.keys filter {
//       muxName => trueShadows(muxName).nonEmpty || falseShadows(muxName).nonEmpty
//     }).toSet
//     // set of signals in shadows
//     val shadowedSigs = (shadows flatMap { case (muxName, tShadow, fShadow) => {
//       if (shadowedMuxes.contains(muxName)) tShadow ++ fShadow
//       else Seq()
//     }}).toSet
//     if (indentLevel == 1) println(s"Total shadow size: ${shadowedSigs.size}")
//     // map of name -> original hyperedge
//     val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//     // top level edges (filter out shadows) & make muxes depend on shadow inputs
//     val unshadowedHE = bodyEdges filter {he => !shadowedSigs.contains(he.name)}
//     val topLevelHE = unshadowedHE map { he => {
//       val deps = if (!shadowedMuxes.contains(he.name)) he.deps
//                  else {
//                    val shadowDeps = (trueShadows(he.name) ++ falseShadows(he.name)) flatMap { heMap(_).deps }
//                    he.deps ++ shadowDeps
//                  }
//       // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
//       he.copy(deps = deps.distinct)
//     }}
//     // build graph on new hyperedges and run topo sort
//     val g = buildGraph(topLevelHE)
//     val mergedRegs = g.mergeRegsSafe(regsToConsider)
//     val mergedRegWrites = (mergedRegs map { _ + "$next" }).toSet
//     // Assuming if replacing, only one statement has name, otherwise extra if (upda..
//     def mergeRegUpdateIfPossible(name: String, toEmit: String): String = {
//       val removed = toEmit.replaceAllLiterally("$next", "")
//       if (mergedRegWrites.contains(name)) "if (update_registers) " + removed
//       else toEmit
//     }
//     g.reorderNames foreach { name => {
//       val stmt = heMap(name).stmt
//       if (shadowedMuxes.contains(name)) {
//         def writeShadow(members: Seq[String], muxValExpr: Expression) {
//           // NOTE: not calling writeBodyMuxOpt since regs can't be in shadows
//           writeBodyMuxOpt(indentLevel + 1, members map heMap, doNotShadow, doNotDec)
//           writeLines(indentLevel + 1, mergeRegUpdateIfPossible(name, s"$name = ${emitExpr(muxValExpr)};"))
//         }
//         val muxExpr = muxMap(name)
//         // declare output type
//         val resultTpe = findResultType(stmt)
//         // FUTURE: don't require finding $next in name, change caller to adjust doNotDec
//         if ((!name.endsWith("$next")) && (!doNotDec.contains(name)))
//           writeLines(indentLevel, s"${genCppType(resultTpe)} $name;")
//         writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
//         writeShadow(trueShadows(name), muxExpr.tval)
//         writeLines(indentLevel, "} else {")
//         writeShadow(falseShadows(name), muxExpr.fval)
//         writeLines(indentLevel, "}")
//       } else {
//         writeLines(indentLevel, emitStmt(doNotDec)(stmt) map {mergeRegUpdateIfPossible(name, _)})
//       }
//     }}
//     mergedRegs
//   } else Seq()
// }

// Emitter that zones design in addition to shadowing muxes and merging reg updates
// def writeBodyZoneOpt(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String], resetTree: Seq[String],
//                          topName: String, doNotShadow: Seq[String], memUpdates: Seq[MemUpdate],
//                          extIOtypes: Map[String, Type], regsToConsider: Seq[String]): Seq[String] = {
//   // map of name -> original hyperedge
//   val heMap = (bodyEdges map { he => (he.name, he) }).toMap
//   val regNamesSet = regNames.toSet
//   // calculate zones based on all edges
//   val g = buildGraph(bodyEdges)
//   g.printTopologyStats
//   val mergedRegs = g.mergeRegsSafe(regsToConsider)
//   val zoneMapWithSources = g.findZonesMFFC(doNotShadow)
//   val zoneMapCF = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
//   val gDF = buildGraph(bodyEdges)
//   val zoneMapDF = gDF.remakeZoneMap(zoneMapCF, doNotShadow)
//   gDF.analyzeZoningQuality(zoneMapDF)
//   val inputsToZones = zoneMapDF.flatMap(_._2.inputs).toSet
//   val nodesInZones = zoneMapDF.flatMap(_._2.members).toSet
//   val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
//   val outputsFromZones = zoneMapDF.flatMap(_._2.outputs).toSet.diff(regNamesSet)
//   val outputConsumers = outputConsumerZones(zoneMapDF)
//   val inputRegs = (regNamesSet intersect inputsToZones).toSeq
//   val mergedInRegs = (mergedRegs intersect inputRegs filter { outputConsumers.contains(_) })
//   val regsUncheckedByZones = inputRegs diff mergedInRegs
//   val shouldCheckInZone = (mergedInRegs map { _ + "$next"}).toSet
//   val shouldSetInZone = (mergedRegs map { _ + "$next"}).toSet
//
//   // predeclare output nodes
//   val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
//   val outputPairs = (outputTypes zip outputsFromZones).toSeq
//   val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
//   writeLines(0, preDecs)
//   val doNotDec = outputsFromZones.toSet
//   println(s"Output nodes: ${outputsFromZones.size}")
//
//   // set input flags to true for other inputs (resets, mems, or external IOs)
//   // FUTURE: remove. should make change detection for these inputs so consuming
//   //         zones have a chance to sleep
//   val otherFlags = inputsToZones diff (regNamesSet ++ zoneMapWithSources.flatMap(_._2.outputs).toSet)
//   val memNames = memUpdates map { _.memName }
//   val memFlags = otherFlags intersect memNames.toSet
//   val nonMemFlags = otherFlags diff memNames.toSet
//   // FUTURE: fix, can't be hacking for reset, but reset isn't in signal map table
//   val nonMemFlagTypes = nonMemFlags.toSeq map {
//     name => if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name)
//   }
//   val nonMemPreDecs = (nonMemFlagTypes zip nonMemFlags.toSeq) map {
//     case (tpe, name) => s"${genCppType(tpe)} ${name.replace('.','$')}$$old;"
//   }
//   writeLines(0, nonMemPreDecs)
//
//   // predeclare zone activity flags
//   val zoneNames = zoneMapCF.keys.toSeq
//   writeLines(0, zoneNames map { zoneName => s"bool ${genFlagName(zoneName)};" })
//   println(s"Activity flags: ${zoneNames.size}")
//
//   writeLines(0, s"bool sim_cached = false;")
//   writeLines(0, s"bool regs_set = false;")
//
//   // start emitting eval function
//   writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
//   writeLines(1, "if (reset || !done_reset) {")
//   writeLines(2, "sim_cached = false;")
//   writeLines(2, "regs_set = false;")
//   writeLines(1, "}")
//   writeLines(1, resetTree)
//
//   writeLines(1, "if (!sim_cached) {")
//   writeLines(2, zoneNames map { zoneName => s"${genFlagName(zoneName)} = true;" })
//   writeLines(1, "}")
//   writeLines(1, "sim_cached = regs_set;")
//
//   // do activity detection on other inputs (external IOs and resets)
//   val nonMemChangeDetects = nonMemFlags flatMap { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     genDepZoneTriggers(outputConsumers(sigName), s"$sigName != $oldVersion")
//   }}
//   writeLines(1, nonMemChangeDetects.toSeq)
//   // cache old versions
//   val nonMemCaches = nonMemFlags map { sigName => {
//     val oldVersion = s"${sigName.replace('.','$')}$$old"
//     s"$oldVersion = $sigName;"
//   }}
//   writeLines(1, nonMemCaches.toSeq)
//
//   // compute zone order
//   // map of name -> zone name (if in zone)
//   val nameToZoneName = zoneMapCF flatMap {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       outputs map { portName => (portName, zoneName) }
//   }}
//   // list of super hyperedges for zones
//   val zoneSuperEdges = zoneMapCF map {
//     case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//       HyperedgeDep(zoneName, inputs, heMap(members.head).stmt)
//   }}
//   // list of non-zone hyperedges
//   val nonZoneEdges = bodyEdges filter { he => !nodesInZonesWithSources.contains(he.name) }
//   // list of hyperedges with zone members replaced with zone names
//   val topLevelHE = zoneSuperEdges map { he:HyperedgeDep => {
//     val depsRenamedForZones = (he.deps map {
//       depName => nameToZoneName.getOrElse(depName, depName)
//     }).distinct
//     HyperedgeDep(he.name, depsRenamedForZones, he.stmt)
//   }}
//   // reordered names
//   val gTopLevel = buildGraph(topLevelHE.toSeq)
//   val zonesReordered = gTopLevel.reorderNames
//
//   // emit zone of sources
//   if (zoneMapWithSources.contains("ZONE_SOURCE")) {
//     val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
//     val sourceZoneEdges = sourceZoneInfo.members map heMap
//     // FUTURE: does this need to be made into tail?
//     writeBodyMuxOpt(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
//   }
//
//   // emit each zone
//   zonesReordered map { zoneName => (zoneName, zoneMapDF(zoneName)) } foreach {
//       case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) => {
//     writeLines(1, s"if (${genFlagName(zoneName)}) {")
//     writeLines(2, s"${genFlagName(zoneName)} = false;")
//     val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
//     val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
//     val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
//       s"${genCppType(tpe)} $name$$old = $name;"
//     }}
//     writeLines(2, oldOutputs)
//     val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
//     // FUTURE: shouldn't this be made into tail?
//     writeBodyMuxOpt(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
//     val regsInZone = members filter shouldCheckInZone map { _.replaceAllLiterally("$next","") }
//     val regsTriggerZones = regsInZone flatMap {
//       regName => genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
//     }
//     writeLines(2, regsTriggerZones)
//     val outputTriggers = outputsCleaned flatMap {
//       name => genDepZoneTriggers(outputConsumers(name), s"$name != $name$$old")
//     }
//     writeLines(2, outputTriggers)
//     val regsToUpdate = members filter shouldSetInZone map { _.replaceAllLiterally("$next","") }
//     writeLines(2, regsToUpdate map { regName => s"$regName = $regName$$next;" })
//     writeLines(1, "}")
//   }}
//
//   // emit rest of body (without redeclaring)
//   // FUTURE: does this need to be made into tail?
//   writeBodyMuxOpt(1, nonZoneEdges, doNotShadow, doNotDec)
//
//   // trigger zones based on mem writes
//   // NOTE: if mem has multiple write ports, either can trigger wakeups
//   val memEnablesAndMasks = (memUpdates map {
//     mu => (mu.memName, Seq(mu.wrEnName, mu.wrMaskName))
//   }).toMap
//   val memWriteTriggerZones = memFlags.toSeq flatMap { flagName => {
//     val condition = memEnablesAndMasks(flagName).mkString(" && ");
//     genDepZoneTriggers(outputConsumers(flagName), condition)
//   }}
//   writeLines(1, memWriteTriggerZones)
//
//   val regsTriggerZones = regsUncheckedByZones.toSeq flatMap { regName => {
//     if (outputConsumers.contains(regName))
//       genDepZoneTriggers(outputConsumers(regName), s"$regName != $regName$$next")
//     else Seq()
//   }}
//   writeLines(1, regsTriggerZones)
//   mergedRegs
// }

// case class MemUpdate(memName: String, wrEnName: String, wrMaskName: String,
//                      wrAddrName: String, wrDataName: String)

// def addMemDepsToGraph(g: Graph, memUpdates: Seq[MemUpdate]) {
//   // FUTURE: does not handle multiple write ports to same mem
//   memUpdates foreach {
//     mu => g.addNodeWithDeps(mu.memName + "$next", findDependencesMemWrite(mu))
//   }
// }

// def generateMemUpdates(bodies: Seq[Statement]): Seq[MemUpdate] = {
//   bodies flatMap { body =>
//     val memories = findMemory(body)
//     memories foreach {m =>
//       if(!memHasRightParams(m)) throw new Exception(s"improper mem! $m")}
//     val memConnects = grabMemInfo(body).toMap
//     val memWriteCommands = memories flatMap {m: DefMemory => {
//       m.writers map { writePortName:String => {
//         val wrEnName = memConnects(s"${m.name}.$writePortName.en")
//         val wrAddrName = memConnects(s"${m.name}.$writePortName.addr")
//         val wrDataName = memConnects(s"${m.name}.$writePortName.data")
//         val wrMaskName = memConnects(s"${m.name}.$writePortName.mask")
//         MemUpdate(m.name, wrEnName, wrMaskName, wrAddrName, wrDataName)
//       }}
//     }}
//     memWriteCommands
//   }
// }

// def emitMemUpdate(mu: MemUpdate) = {
//   s"if (${mu.wrEnName} && ${mu.wrMaskName}) ${mu.memName}[${mu.wrAddrName}.as_single_word()] = ${mu.wrDataName};"
// }

// def findDependencesMemWrite(mu: MemUpdate): Seq[String] = {
//   val deps = Seq(mu.wrEnName, mu.wrMaskName, mu.wrAddrName, mu.wrDataName)
//   (deps filter { name => !name.startsWith("UInt<1>(0x") }).distinct
// }



// from Graph.scala

// def findZones(regNames: Seq[String]) = {
//   val regIDs = regNames flatMap {name =>
//     if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   val zones = ArrayBuffer.fill(nameToID.size)(-1)
//   regIDs foreach { id => zones(id) = id }
//   (0 until zones.size) foreach {
//     id => if ((zones(id) == -1) && (inNeigh(id).size == 0) &&
//               validNodes.contains(id))
//                 zones(id) = -2
//   }
//   growZones(regIDs, zones)
//   mergeZones(zones, regIDsSet)
//   val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 && p._1 != -2}
//   val skipSelf = skipUnreached filter { p => p._1 != p._2 }
//   val zonesGrouped = skipSelf groupBy { _._1 }
//   val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
//   val useNames = zoneMap map { case (k,v) => (idToName(k), v map idToName) }
//   useNames
// }



// def growZones(frontier: Seq[Int], zones: ArrayBuffer[Int]): ArrayBuffer[Int] = {
//   // println(s"${(zones filter {_ == -1}).size} / ${zones.size}")
//   if (frontier.isEmpty) zones
//   else {
//     val nextFrontier = frontier flatMap { id =>
//       outNeigh(id) flatMap { neigh => {
//         if ((zones(neigh) == -1) && (inNeigh(neigh) forall { nneigh =>
//                 (zones(nneigh) == zones(id)) || (zones(nneigh) == -2)})) {
//           // inNeigh(neigh) foreach {
//           //   nneigh => if (zones(nneigh) == -2) zones(nneigh) = zones(id)}
//           zones(neigh) = zones(id)
//           Seq(neigh)
//         } else Seq()
//     }}}
//     growZones(nextFrontier, zones)
//   }
// }



// def mergeZones(zones: ArrayBuffer[Int], regIDsSet: Set[Int]) {
//   val cutoff = 10
//   // warning, cutoff set manually in Compiler.scala
//   val fringe = (0 until zones.size) filter { id => (zones(id) == -1) &&
//                   (inNeigh(id).forall {
//                     neigh => (zones(neigh) != -1) && (zones(neigh) != -2)})
//   }
//   // FUTURE: maybe want to allow fringe to be -2 descendants
//   println(fringe.size)
//   val mergesWanted = fringe map {id => inNeigh(id).map(zones(_)).distinct}
//   val mergesCleaned = mergesWanted filter { !_.isEmpty }
//   val numRegsInZones = (zones.zipWithIndex filter { p: (Int, Int) =>
//     regIDsSet.contains(p._2) }).groupBy(_._1).mapValues{_.size}
//   if (!mergesCleaned.isEmpty) {
//     def mergedSize(mergeReq: Seq[Int]) = (mergeReq map numRegsInZones).sum
//     val zonesToMerge = mergesCleaned.reduceLeft{ (p1,p2) =>
//       if (mergedSize(p1) < mergedSize(p2)) p1 else p2
//     }
//     val newSize = zonesToMerge.map{numRegsInZones(_)}.sum
//     if (newSize < cutoff) {
//       println(s"Zone sizes ${(zonesToMerge map numRegsInZones).mkString("+")}")
//       zonesToMerge foreach {zone => println(idToName(zone)) }
//       val renameMap = (zonesToMerge.tail map { (_, zonesToMerge.head) }).toMap
//       (0 until zones.size) foreach { id =>
//         if (renameMap.contains(zones(id))) zones(id) = renameMap(zones(id))}
//       val newFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
//       growZones(newFront, zones)
//       val numZones = zones.groupBy(i => i).values.filter(_.size > cutoff).size
//       println(s"distinct: $numZones")
//       mergeZones(zones, regIDsSet)
//     }
//   }
// }



// def mergeZonesML(zones: ArrayBuffer[Int], regIDsSet: Set[Int], frozenZones: Set[Int]) {
//   val cutoff = 16
//   val fringe = (0 until zones.size) filter { id =>
//                   (zones(id) == -1) &&
//                   (inNeigh(id) forall { neigh => zones(neigh) != -1 } )
//   }
//   println(s"Finge size: ${fringe.size}")
//   val mergesWanted = fringe map {id => inNeigh(id).map(zones(_)).distinct}
//   val mergesCleaned = mergesWanted map {_ filter {_ != -2}} filter { !_.isEmpty } filter { _ forall { !frozenZones.contains(_)}}
//   // map from zone ID to seq of member ids
//   val zoneMap = zones.zipWithIndex.groupBy(_._1) mapValues { _ map {_._2} }
//   // number of zone inputs as signals (registers in future)
//   val inDegreeToZone = zoneMap mapValues { zoneMembers =>
//     (zoneMembers.flatMap{ inNeigh(_) }.toSeq.distinct diff zoneMembers).size
//   }
//   if (!mergesCleaned.isEmpty) {
//     def mergedSize(mergeReq: Seq[Int]) = (mergeReq map inDegreeToZone).sum
//     // using reduce left to find smallest new merged zone
//     val zonesToMerge = mergesCleaned.reduceLeft{ (p1,p2) =>
//       if (mergedSize(p1) < mergedSize(p2)) p1 else p2
//     }
//     val newSize = zonesToMerge.map{inDegreeToZone(_)}.sum
//     if (newSize < cutoff) {
//       println(s"Zone sizes ${(zonesToMerge map inDegreeToZone).mkString("+")}")
//       zonesToMerge foreach {zone => println(idToName(zone)) }
//       val renameMap = (zonesToMerge.tail map { (_, zonesToMerge.head) }).toMap
//       (0 until zones.size) foreach { id =>
//         if (renameMap.contains(zones(id))) zones(id) = renameMap(zones(id))}
//       val newFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
//       growZones(newFront, zones)
//       val numZones = zones.groupBy(i => i).values.filter(_.size > cutoff).size
//       println(s"distinct: $numZones")
//       mergeZonesML(zones, regIDsSet, frozenZones)
//     }
//   }
// }



// def findZonesML(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
//   val regIDs = regNames flatMap {name =>
//   if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
//   val zones = ArrayBuffer.fill(nameToID.size)(-1)
//   regIDs foreach { id => zones(id) = id }
//   val otherZoneSeeds = (0 until zones.size) filter {
//     id => (zones(id) == -1) && (inNeigh(id).size == 0) && !validNodes.contains(id)
//   }
//   otherZoneSeeds foreach { id => zones(id) = id }
//   val sourceZoneSeeds = (0 until zones.size) filter {
//     id => (zones(id) == -1) && (inNeigh(id).size == 0) && validNodes.contains(id)
//   }
//   sourceZoneSeeds foreach { zones(_) = -2 }
//   growZones(sourceZoneSeeds, zones)
//   val firstFront = (0 until zones.size) filter { id => (zones(id) == -1) && validNodes.contains(id) &&
//                     (inNeigh(id).forall { parent => (zones(parent) != -1) })
//   }
//   firstFront foreach { id => zones(id) = id }
//   val startingFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
//   growZones(startingFront, zones)
//   mergeZonesML(zones, regIDsSet, regIDsSet)
//   (0 until 3) foreach { n => {
//     println(s"doing layer $n")
//     findZonesMLHelper(zones, regIDsSet)
//   }}
//   val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 }
//   // val skipSelf = skipUnreached filter { p => p._1 != p._2 }
//   val zonesGrouped = skipUnreached groupBy { _._1 }
//   val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
//   // val smallZonesRemoved = zoneMap filter { _._2.size > 10 }
//   val smallZonesRemoved = zoneMap filter {
//     case (name,members) => !(members filter validNodes).isEmpty
//   }
//   smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
//     val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
//     val inputNames = zoneInputs(validMembers) map idToName
//     val memberNames = validMembers map idToName
//     val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
//     val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
//     (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
//   }}
// }



// def findZonesMLHelper(zones: ArrayBuffer[Int], regIDsSet: Set[Int]) {
//   val frozenZones = zones.toSet
//   val frontier = (0 until zones.size) filter { id => (zones(id) == -1) &&
//                     (inNeigh(id).forall { neigh => (zones(neigh) != -1) })
//   }
//   frontier foreach { id => zones(id) = id }
//   growZones(frontier, zones)
//   mergeZonesML(zones, regIDsSet, frozenZones)
// }



// def findLoopbackRegs(regNames: Seq[String], zoneMap: Map[Int,Seq[Int]], zones: ArrayBuffer[Int]): Seq[String] = {
//   val includedRegWrites = regNames filter {
//     regName => nameToID.contains(regName) && nameToID.contains(regName + "$next")
//   }
//   println(s"${includedRegWrites.size}/${regNames.size} registers have zone for $$next")
//   val regsInLoopbackZones = includedRegWrites filter { regName => {
//     val writeZoneID = zones(nameToID(regName + "$next"))
//     val writeZoneInputs = zoneInputs(zoneMap(writeZoneID) filter { validNodes.contains(_) })
//     writeZoneInputs.contains(nameToID(regName))
//   }}
//   println(s"${regsInLoopbackZones.size} registers have same zone input and output")
//   regsInLoopbackZones
// }



// def loopBackRegsSafeToMerge(regNames: Seq[String], zoneMap: Map[Int,Seq[Int]], zones: ArrayBuffer[Int]): Seq[String] = {
//   val loopbackRegs = findLoopbackRegs(regNames, zoneMap, zones)
//   val loopbackIDs = (loopbackRegs map nameToID).toSet
//   val zoneGraph = buildZoneGraph(zoneMap, zones)
//   val regInputZoneNamePairs = zoneMap.toSeq flatMap { case (zoneID, members) => {
//     val inputs = zoneInputs(members filter { validNodes.contains(_) })
//     val regInputs = loopbackIDs.intersect(inputs.toSet)
//     regInputs.toSeq map { (_, zoneID) }
//   }}
//   val regIDtoConsumingZones = (regInputZoneNamePairs.groupBy(_._1).map {
//     case (regID, pairs) => (regID, pairs map { _._2 })
//   }).toMap
//   val safeToMergeRegs = loopbackRegs filter { regName => {
//     val regID = nameToID(regName)
//     val writeZoneID = zones(nameToID(regName + "$next"))
//     val writeZoneName = idToName(writeZoneID)
//     val siblingZones = regIDtoConsumingZones(regID) diff Seq(writeZoneID)
//     // Checks that no path from reg consuming zone to reg writing zone
//     // siblingZones forall { sibZoneID => {
//     //   val sibZoneName = idToName(sibZoneID)
//     //   !zoneGraph.extPathExists(Seq(zoneGraph.nameToID(sibZoneName)), Seq(zoneGraph.nameToID(writeZoneName)))}
//     // }
//     // Checks that no path from reg writing zone to any reg reading zone
//     siblingZones forall { sibZoneID => {
//       val sibZoneName = idToName(sibZoneID)
//       !zoneGraph.extPathExists(Seq(zoneGraph.nameToID(writeZoneName)), Seq(zoneGraph.nameToID(sibZoneName)))}
//     }
//   }}
//   println(s"${safeToMergeRegs.size} registers can be safely merged into write zones")
//   // NOTE: still an overestimate since testing safety individually
//   safeToMergeRegs
// }



// def mergeInLoopbackRegs(regNames: Seq[String], zoneMap: Map[Int,Seq[Int]], zones: ArrayBuffer[Int]) {
//   val loopbackRegs = loopBackRegsSafeToMerge(regNames, zoneMap, zones)
//   val loopbackRegIDs = loopbackRegs map nameToID
//   loopbackRegIDs foreach { regID => zones(regID) = regID }
//   val zoneMapWithRegs = zones.zipWithIndex.groupBy(_._1) mapValues { _ map {_._2} }
//   val zoneGraph = buildZoneGraph(zoneMapWithRegs, zones)
//   val cyclesFound = zoneGraph.topologicalSortFindCycles
//   println(s"Adding loopback regs to zone graphs creates ${cyclesFound.size} cycles")
//   val loopbackMerges = loopbackRegs map { regName => {
//     val regID = nameToID(regName)
//     val writeZoneID = zones(nameToID(regName + "$next"))
//     Seq(writeZoneID, regID)
//   }}
//   val newZoneMap = mergeZonesSafe(loopbackMerges, zoneGraph, zoneMapWithRegs, zones)
//   val zonesMerged = zoneMapWithRegs.size - newZoneMap.size
//   println(s"Was able to merge $zonesMerged/${loopbackRegs.size} loopback reg zones")
//   val (mergedRegs, unMergedRegs) = loopbackRegIDs partition { regID => zones(regID) != regID }
//   println(s"Merged: ${mergedRegs.size} Unmerged: ${unMergedRegs.size}")
//   // unMergedRegs foreach { id => println(idToName(id)) }
//   val zoneGraph2 = buildZoneGraph(newZoneMap, zones)
//   val cyclesFound2 = zoneGraph.topologicalSortFindCycles
//   println(s"Merging safe loopback regs creates ${cyclesFound.size} cycles")
// }



// FUTURE: may be able to eliminate. safety condition possibly too pessimistic
// def loopBackRegsCycleCheck(regNames: Seq[String], zoneMap: Map[Int,Seq[Int]], zones: ArrayBuffer[Int]) {
//   val loopbackRegs = loopBackRegsSafeToMerge(regNames, zoneMap, zones)
//   loopbackRegs foreach { regName => {
//     val regID = nameToID(regName)
//     val writeZoneID = zones(nameToID(regName + "$next"))
//     zones(regID) = writeZoneID
//   }}
//   val zoneMapWithStateCycles = zones.zipWithIndex.groupBy(_._1) mapValues { _ map {_._2} }
//   val zoneGraph = buildZoneGraph(zoneMapWithStateCycles, zones)
//   val cyclesFound = zoneGraph.topologicalSortFindCycles
//   println(s"Found ${cyclesFound.size} cycles")
//   // val cyclesFoundTranslated = cyclesFound map { _ map { zoneGraphID => nameToID(zoneGraph.idToName(zoneGraphID)) }}
//   val cyclesFoundTranslated = cyclesFound map { _ map { zoneGraphID => zoneGraph.idToName(zoneGraphID) }}
//   val regNamesInZone = loopbackRegs groupBy { regName => { zones(nameToID(regName)) }}
//   val regsInZone = regNamesInZone map { case (zoneID, regNames) => (zoneID, regNames map nameToID) }
//   val regsToDrop = cyclesFoundTranslated flatMap { cycleMembers => {
//     val impactfulRegs = regsToUnzone(cycleMembers :+ cycleMembers.head, regsInZone, zoneMapWithStateCycles)
//     // FUTURE: use heuristics to pick best to drop
//     if (impactfulRegs.isEmpty) Seq()
//     else Seq(impactfulRegs.head)
//   }}
//   println(s"found ${regsToDrop.size} regs to remove")
//   regsToDrop foreach { zones(_) = -2 }
//   val loopbackRegs2 = loopbackRegs diff regsToDrop
//   val zoneMapWithStateCycles2 = zones.zipWithIndex.groupBy(_._1) mapValues { _ map {_._2} }
//   val zoneGraph2 = buildZoneGraph(zoneMapWithStateCycles2, zones)
//   val cyclesFound2 = zoneGraph2.topologicalSortFindCycles
//   println(s"Found ${cyclesFound2.size} cycles")
//   // val zoneOrder = zoneGraph.reorderNames
//   // println("Zone graph is acyclic and successfully ordered zones")
// }



// don't forget to make input cyclic by appending copy of head
// want to use zoneMap with state added in
// def regsToUnzone(cycleNames: Seq[String], regsInZone: Map[Int,Seq[Int]], zoneMap: Map[Int,Seq[Int]]): Seq[Int] = {
//   if (cycleNames.isEmpty || cycleNames.size == 1) Seq()
//   else {
//     val parentZoneID = nameToID(cycleNames.head)
//     val childZoneID = nameToID(cycleNames(1))
//     val childInputs = zoneInputs(zoneMap(childZoneID) filter { validNodes.contains(_) })
//     val childInputsFromParent = childInputs filter { zoneMap(parentZoneID).contains(_) }
//     val regDescendants = childInputsFromParent.intersect(regsInZone.getOrElse(parentZoneID,Seq()))
//     if (regDescendants.size == 1) Seq(regDescendants.head) ++ regsToUnzone(cycleNames.tail, regsInZone, zoneMap)
//     else regsToUnzone(cycleNames.tail, regsInZone, zoneMap)
//     // FUTURE: handle case when it takes more than one reg
//   }
// }



// makes zones by evenly splitting output of topo sort
// def findZonesTopo(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
//   val numParts = 1000
//   val topoOrder = topologicalSort()
//   val partSize = topoOrder.size / numParts
//   val intoParts = topoOrder.grouped(partSize).toSeq
//   val zoneMap = (intoParts map { l => (l.head, l) }).toMap
//   val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
//   val smallZonesRemoved = zoneMap filter {
//     case (name,members) => !(members filter validNodes).isEmpty
//   }
//   smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
//     val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
//     val inputNames = zoneInputs(validMembers) map idToName
//     val memberNames = validMembers map idToName
//     val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
//     val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
//     (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
//   }}
// }



// makes zones by splitting output of topo sort every time a new search is started
// def findZonesTopo2(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
//   val topoOrder = topologicalSort()
//   val regIDs = regNames flatMap {name =>
//     if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
//   regIDs foreach {regID => startingDepths(regID) = 0}
//   val depths = stepBFSDepth(regIDsSet, startingDepths)
//   val topoSearches = topoOrder.foldLeft((100, Seq[Seq[Int]]())) {
//     case ((lastDepth:Int , partList:Seq[Seq[Int]]), id:Int) => {
//       if (depths(id) < lastDepth) (depths(id), partList :+ Seq(id))
//       else (depths(id), partList.init :+ (partList.last :+ id))
//   }}._2
//   val zoneMap = (topoSearches map { l => (l.head, l) }).toMap
//   val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
//   val smallZonesRemoved = zoneMap filter {
//     case (name,members) => !(members filter validNodes).isEmpty
//   }
//   smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
//     val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
//     val inputNames = zoneInputs(validMembers) map idToName
//     val memberNames = validMembers map idToName
//     val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
//     val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
//     (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
//   }}
// }



// makes zones by splitting output of topo sort every time a new search is started, then clumps them
// def findZonesTopo3(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
//   val numParts = 1000
//   val topoOrder = topologicalSort()
//   val partSize = topoOrder.size / numParts
//   val regIDs = regNames flatMap {name =>
//     if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
//   regIDs foreach {regID => startingDepths(regID) = 0}
//   val depths = stepBFSDepth(regIDsSet, startingDepths)
//   val topoSearches = topoOrder.foldLeft((100, Seq[Seq[Int]]())) {
//     case ((lastDepth:Int , partList:Seq[Seq[Int]]), id:Int) => {
//       if (depths(id) < lastDepth) (depths(id), partList :+ Seq(id))
//       else (depths(id), partList.init :+ (partList.last :+ id))
//   }}._2
//   val clumped = topoSearches.tail.foldLeft(Seq[Seq[Int]](topoSearches.head)) {
//     case (partList:Seq[Seq[Int]], currPart:Seq[Int]) => {
//       if (partList.last.size > partSize) partList :+ currPart
//       else partList.init :+ (partList.last ++ currPart)
//   }}
//   val zoneMap = (clumped map { l => (l.head, l) }).toMap
//   val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
//   val smallZonesRemoved = zoneMap filter {
//     case (name,members) => !(members filter validNodes).isEmpty
//   }
//   smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
//     val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
//     val inputNames = zoneInputs(validMembers) map idToName
//     val memberNames = validMembers map idToName
//     val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
//     val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
//     (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
//   }}
// }



// def partialCutCost(order: Seq[Int], orderInv: Map[Int,Int], currStart: Int,
//                    desiredEnd: Int) = {
//   val nodesExposed = (currStart until desiredEnd) map order
//   val nodeDests = nodesExposed flatMap { id => outNeigh(id) }
//   val destsPastEnd = nodeDests map orderInv filter { _ >= desiredEnd }
//   destsPastEnd.toSet.size
// }



// def pickBestSplit(order: Seq[Int], orderInv: Map[Int,Int], scoresWithSplits: Seq[(Int,Int)],
//                   lastScoreIndex: Int, maxPartSize: Int) = {
//   def splitCost(splitAt: Int) = scoresWithSplits(splitAt)._1 +
//                   partialCutCost(order, orderInv, splitAt, lastScoreIndex + 1)
//   val nodesToConsider = (math.max(0, lastScoreIndex-maxPartSize) to lastScoreIndex)
//   val costsWithNodes = nodesToConsider map { id => (splitCost(id), id)}
//   def minPair(pA: (Int,Int), pB: (Int,Int)) = {
//     if (pA < pB) pA
//     else pB
//   }
//   costsWithNodes.reduceLeft(minPair)
// }



// def kernHelper(order: Seq[Int], orderInv: Map[Int,Int], maxPartSize: Int,
//                scoresWithSplits: Seq[(Int,Int)]): Seq[(Int,Int)] = {
//   if (scoresWithSplits.size < order.size) {
//     val (lowestScore, splitIndex) = pickBestSplit(order, orderInv,
//                                       scoresWithSplits, scoresWithSplits.size - 1, maxPartSize)
//     kernHelper(order, orderInv, maxPartSize, scoresWithSplits :+ (lowestScore, splitIndex))
//   } else scoresWithSplits
// }



// def pickOutSplits(scoresWithSplits: Seq[(Int,Int)], currIndex: Int): Seq[Int] = {
//   val topoID = scoresWithSplits(currIndex)._2
//   if (topoID > 0) Seq(topoID) ++ pickOutSplits(scoresWithSplits, topoID)
//   else Seq(topoID)
// }



// def splitUpSeq(l: Seq[Int], splits: Seq[Int], offset: Int=0): Seq[Seq[Int]] = {
//   val globalIndex = splits.head
//   val (part, rest) = l.splitAt(globalIndex - offset)
//   if (splits.tail.isEmpty) Seq(part)
//   else Seq(part) ++ splitUpSeq(rest, splits.tail, globalIndex)
// }



// make zones from Kernigan approach after topo sorting graph
// def findZonesKern(regNames: Seq[String], doNotShadow: Seq[String]) = {
//   val maxPartSize = 50
//   val topoOrder = topologicalSort()
//   val getOrderID = topoOrder.zipWithIndex.toMap
//   val scoresWithSplits = kernHelper(topoOrder, getOrderID, maxPartSize, Seq((0,topoOrder.size)))
//   val splitIndices = pickOutSplits(scoresWithSplits, scoresWithSplits.size-1).reverse
//   val intoParts = splitUpSeq(topoOrder, splitIndices) filter { !_.isEmpty }
//   val zoneMap = (intoParts map { l => (l.head, l) }).toMap
//   val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
//   val smallZonesRemoved = zoneMap filter {
//     case (name,members) => !(members filter validNodes).isEmpty
//   }
//   smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
//     val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
//     val inputNames = zoneInputs(validMembers) map idToName
//     val memberNames = validMembers map idToName
//     val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
//     val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
//     (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
//   }}
// }



// def RCMordering() = {
//   // Find depth 0 nodes to seed search
//   val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
//   val sourceNodes = (0 until inNeigh.size) filter { inNeigh(_).size == 0 }
//   sourceNodes foreach {id => startingDepths(id) = 0}
//   val depths = stepBFSDepth(sourceNodes.toSet, startingDepths)
//   val depth0Nodes = depths.zipWithIndex.collect{ case (d,i) if d == 0 => i}
//   // Order initial frontier ascending by degree
//   val sortedByOutDegree = sortByOutDegree(depth0Nodes)
//   val visited = ArrayBuffer.fill(nameToID.size)(false)
//   sortedByOutDegree foreach { visited(_) = true }
//   val orderedIDs = RCMstep(sortedByOutDegree, visited).reverse
//   orderedIDs filter { validNodes } map idToName
// }



// def sortByOutDegree(nodes: Seq[Int]) = {
//   nodes map { id => (id, outNeigh(id).size) } sortBy { _._2 } map { _._1 }
// }



// def RCMstep(frontier: Seq[Int], visited: ArrayBuffer[Boolean]): Seq[Int] = {
//   val newFront = frontier flatMap { id => {
//     val childrenToAdd = outNeigh(id) filter { !visited(_) }
//     val childrenOrdered = sortByOutDegree(childrenToAdd)
//     childrenOrdered foreach { visited(_) = true }
//     childrenOrdered
//   }}
//   if (newFront.isEmpty) frontier
//   else frontier ++ RCMstep(newFront, visited)
// }



// def doubleOrdering() = {
//   val identityOrder = ((0 until outNeigh.size) map identity).toSeq
//   doDoubleOrder(identityOrder,5) filter validNodes map idToName
// }



// def doDoubleOrder(initialOrder: Seq[Int], times: Int): Seq[Int] = {
//   println(s"$times to go")
//   if (times == 0) initialOrder
//   else {
//     val rowAdj = renameGraph(outNeigh, initialOrder)
//     val rowOrder = sortGraph(rowAdj)
//     val colAdj = renameGraph(inNeigh, rowOrder)
//     val colOrder = sortGraph(colAdj)
//     // val newOrder = rowOrder.zipWithIndex.toMap
//     // rowOrder.zipWithIndex foreach { case(oldID, newID) => {
//     //   if (!outNeigh(oldID).isEmpty)
//     //     // println(s"$newID ${outNeigh(oldID).head}")
//     //     println(s"$newID ${newOrder(outNeigh(oldID).head)}")
//     // }}
//     doDoubleOrder(colOrder, times - 1)
//   }
// }



// returns bool if idA's adjacencies are lower than idB
// def nodeOrder(idA: Int, idB: Int, adjMap: Map[Int, Seq[Int]], index: Int=0): Boolean = {
//   // FUTURE: contemplate right outcome for running out of neighbors
//   if ((adjMap(idA).size <= index) || (adjMap(idB).size <= index))
//     (adjMap(idA).size < adjMap(idB).size)
//   else if (adjMap(idA)(index) == adjMap(idB)(index))
//     nodeOrder(idA, idB, adjMap, index+1)
//   else adjMap(idA)(index) < adjMap(idB)(index)
// }



// sorts the vertex IDs based on adjacencies and returns new order
// def sortGraph(adjMap: Map[Int, Seq[Int]]): Seq[Int] = {
//   val nodeIDs = (0 until outNeigh.size).toSeq
//   nodeIDs sortWith { (idA:Int, idB:Int) => nodeOrder(idA, idB, adjMap) }
// }



// returns new adjacency list with renames done and neighbors sorted
// renames is oldIDs in new order, so seq maps newID -> oldID
// def renameGraph(adjList: ArrayBuffer[ArrayBuffer[Int]], renames: Seq[Int]) = {
//   // val renameMap = (renames.zipWithIndex map { _.swap }).toMap
//   val renameMap = renames.zipWithIndex.toMap
//   val renamedAdjMap = ((0 until outNeigh.size) map { oldID: Int => {
//     val neighborsRenamed = adjList(oldID) map renameMap
//     (renameMap(oldID), neighborsRenamed.sorted)
//   }}).toMap
//   renamedAdjMap
// }



// def writeHmetisFile(filename: String, regIDs: Seq[Int],
//                     grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
//   // compressing out empty vertices from ID range, and starting at 1
//   val remappedIDs = regIDs.zipWithIndex.toMap.mapValues(_ + 1)
//   val fw = new FileWriter(new File(filename))
//   fw.write(s"${remappedIDs.size} ${grouped.size}\n")
//   grouped foreach { case (triggerSet, children) => {
//     val triggersRemapped = triggerSet.toSeq.map(remappedIDs(_))
//     fw.write(s"""${children.size} ${triggersRemapped.mkString(" ")}\n""")
//   }}
//   fw.close()
//   remappedIDs
// }



// def generateHmetisRegZones(numZones:Int, regIDs: Seq[Int],
//                     grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
//   // build input for hmetis
//   val filename = "regfile.hm"
//   val remappedIDs = writeHmetisFile(filename, regIDs, grouped)
//   val metisPath = "/Users/sbeamer/Downloads/hmetis-1.5-osx-i686/shmetis"
//   val ubFactor = 10
//   // run hmetis
//   s"$metisPath regfile.hm $numZones $ubFactor".!
//   // parse hmetis output
//   val newPartIDs = Source.fromFile(s"$filename.part.$numZones").getLines.toList
//   // undo vertex ID remapping and clump register sets
//   val unmapIDs = remappedIDs.map(_.swap)
//   val partRegIDPairs = newPartIDs zip ((1 to regIDs.size) map { unmapIDs(_) })
//   val regGroups = partRegIDPairs.groupBy(_._1).mapValues(_.map(_._2)).values
//   // regGroups foreach {
//   //   group => println("\n" + group.map(idToName(_)).mkString(","))
//   // }
//   regGroups
// }



// def findZonesHmetis(regNames: Seq[String]) = {
//   val regIDs = regNames flatMap {name =>
//     if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   // for all registers, perform BFS and mark reachable (could do in parallel)
//   val startingSources = ArrayBuffer.fill(nameToID.size)(Set[Int]())
//   regIDs foreach {regID => startingSources(regID) = Set(regID)}
//   val finalSources = stepBFSZone(regIDsSet, startingSources)
//   // set of inputs -> contained nodes
//   val grouped = finalSources.zipWithIndex.groupBy(_._1).mapValues(_.map(_._2))
//   val startingRegGroups = generateHmetisRegZones(400, regIDs, grouped)
//   val zones = ArrayBuffer.fill(nameToID.size)(-1)
//   startingRegGroups foreach { group => {
//     val groupID = group.min
//     group foreach { regID => zones(regID) = groupID }
//   }}
//   (0 until zones.size) foreach {
//     id => if ((zones(id) == -1) && (inNeigh(id).size == 0) && validNodes.contains(id))
//             zones(id) = -2
//   }
//   growZones(regIDs, zones)
//   val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 && p._1 != -2}
//   val skipSelf = skipUnreached filter { p => p._1 != p._2 }
//   val zonesGrouped = skipSelf groupBy { _._1 }
//   val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
//   val useNames = zoneMap map { case (k,v) => (idToName(k), v map idToName) }
//   useNames
// }



// def findNumKids(regSet: Set[Int], grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
//   grouped.filter{
//     case (k,v) => k.intersect(regSet).size == regSet.size
//   }.values.map(_.size).sum
// }



// def findCoParents(regId: Int, grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
//   grouped.keys.filter(_.contains(regId)).reduceLeft(_ ++ _)
// }



// def scoutZones(regNames: Seq[String]) = {
//   val regIDs = regNames flatMap {name =>
//     if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
//   val regIDsSet = regIDs.toSet
//   // for all registers, perform BFS and mark reachable (could do in parallel)
//   val startingSources = ArrayBuffer.fill(nameToID.size)(Set[Int]())
//   regIDs foreach {regID => startingSources(regID) = Set(regID)}
//   val finalSources = stepBFSZone(regIDsSet, startingSources)
//   // set of inputs -> contained nodes
//   val grouped = finalSources.zipWithIndex.groupBy(_._1).mapValues(_.map(_._2))
//   // println(grouped)
//   // println(regIDs.head)
//   // println(idToName(regIDs.head))
//   // val coParents = findCoParents(regIDs.head, grouped)
//   // println(coParents.size)
//   // println(findNumKids(Set(regIDs.head),grouped))
//   // val commonRegPrefixes = regNames.groupBy{
//   //   s => if (s.contains('_')) s.slice(0,s.lastIndexOf('_')) else s
//   // }
//   // println(commonRegPrefixes)
//   // println(commonRegPrefixes.size)
//   // println(regNames.size)
//   // println(startingSources.size)
//   // println(finalSources.map(_.size).reduceLeft(_ + _))
//   // println(grouped.size)
//   // finalSources.zipWithIndex.foreach {
//   //   case (sources, id) => println(s"${idToName(id)} ${sources.size}")
//   // }
//   // println(zoneInputs(Seq(34814, 34817, 34948, 34973)))
//   // println(zoneOutputs(Seq(34814, 34817, 34948, 34973)))
//   // println(finalSources.filter(_.contains(nameToID("dut.T_3641"))).size)
//   // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.core.csr.T_5611"))).size)
//   // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.icache.s1_pc_"))).size)
//   // println(finalSources.filter(_.contains(nameToID("dut.coreplex.DebugModule_1.dbStateReg"))).size)
//   // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.core.csr.T_5600"))).size)
//   // val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
//   // regIDs foreach {regID => startingDepths(regID) = 0}
//   // val depths = stepBFSDepth(regIDsSet, startingDepths)
//   // val unreachable = depths.zipWithIndex filter { _._1 == -1 } map { _._2 }
//   // println(unreachable.size)
//   // unreachable foreach { id => println(idToName(id)) }
//   // depths.zipWithIndex.foreach {
//   //   case (depth, id) => println(s"${idToName(id)} $depth")
//   // }
//   // println(depths reduceLeft (_ max _))
// }



// def GenReversedChain(n: Int) = {
//   val nodeRange = Seq.range(0,n)
//   val offset = 1
//   val offsetRange = nodeRange.drop(offset) ++ nodeRange.take(offset)
//   val edgeList = scala.util.Random.shuffle(nodeRange zip offsetRange)
//   val g = new Graph
//   edgeList.init foreach { case (idA, idB) => g.addNodeWithDeps("s" + idA, Seq("s" + idB)) }
//   g.printTopologyStats()
//   g
// }



// Doesn't necessarily find all cycles
// def topologicalSortFindCycles() = {
//   val cyclesFound = ArrayBuffer[Seq[Int]]()
//   val temporaryMarks = ArrayBuffer.fill(nameToID.size)(false)
//   val finalMarks = ArrayBuffer.fill(nameToID.size)(false)
//   val callerIDs = ArrayBuffer.fill(nameToID.size)(-1)
//   def visit(vertexID: Int, callerID: Int) {
//     if (temporaryMarks(vertexID)) {
//       val cycleFound = findCycle(callerID, callerIDs)
//       val minInCycle = cycleFound reduceLeft ( _ min _ )
//       if (vertexID == minInCycle) {
//         if (confirmCycle(cycleFound :+ cycleFound.head))
//           cyclesFound += cycleFound
//         else
//           println("unconfirmed")
//       }
//     } else if (!finalMarks(vertexID)) {
//       if (vertexID != callerID)
//         callerIDs(vertexID) = callerID
//       temporaryMarks(vertexID) = true
//       inNeigh(vertexID) foreach { neighborID => visit(neighborID, vertexID) }
//       finalMarks(vertexID) = true
//       temporaryMarks(vertexID) = false
//     }
//   }
//   nameToID.values foreach { startingID => visit(startingID, startingID) }
//   cyclesFound
// }



// def findCycle(vertexID: Int, callerIDs: ArrayBuffer[Int], cycleSoFar: Set[Int] = Set[Int]()): Seq[Int] = {
//   if (callerIDs(vertexID) != -1) {
//     if (outNeigh(vertexID).forall(!cycleSoFar.contains(_)))
//       Seq(vertexID) ++ findCycle(callerIDs(vertexID), callerIDs, cycleSoFar + vertexID)
//     else
//       Seq(vertexID)
//   } else Seq()
// }



// for input, don't forget to append copy of head to tail to complete cycle
// def confirmCycle(cycleIDs: Seq[Int]): Boolean = {
//   if (cycleIDs.isEmpty || cycleIDs.size == 1) true
//   else {
//     val currID = cycleIDs.head
//     val nextID = cycleIDs.tail.head
//     if (outNeigh(currID).contains(nextID)) confirmCycle(cycleIDs.tail)
//     else false
//   }
// }




// from Emitter.scala
// Helper methods for building eval bodies
// def grabMemInfo(s: Statement): Seq[(String, String)] = s match {
//   case b: Block => b.stmts flatMap {s: Statement => grabMemInfo(s)}
//   case c: Connect => {
//     firrtl.Utils.kind(c.loc) match {
//       case firrtl.MemKind => Seq((emitExpr(c.loc), emitExpr(c.expr)))
//       case _ => Seq()
//     }
//   }
//   case _ => Seq()
// }




// from Compiler.scala (for tracking mem write activities)

// cache mem inputs and addresses (for mem activity scouting)
// val memAddrs = (memWrites map { _.wrAddr }).distinct
// val memDatas = (memWrites map { _.wrData }).distinct
// val memAddrAndDataCaches = (memAddrs ++ memDatas) flatMap { e => {
//   if (e.isInstanceOf[Literal]) Seq()
//   else {
//     val name = emitExpr(e)
//     Seq(s"${genCppType(e.tpe)} ${name.replace('.','$')}$$old = $name;")
//   }
// }}
// writeLines(1, memAddrAndDataCaches)

// count changes on mem write inputs (for mem activity scouting)
// val memAddrAndDataDetects = memWrites map { mw => {
//   def compStr(e: Expression) = {
//     val name = emitExpr(e)
//     if (e.isInstanceOf[Literal]) "false"
//     else s"$name != ${name.replace('.','$')}$$old"
//   }
//   // s"if (${compStr(mw.wrAddr)} || ${compStr(mw.wrData)}) ${zoneActTrackerName(mw.memName)}++;"
//   s"if (${emitExpr(mw.wrEn)} && ${emitExpr(mw.wrMask)} && (${compStr(mw.wrAddr)} || ${compStr(mw.wrData)})) ${zoneActTrackerName(mw.memName)}++;"
// }}
// writeLines(1, memAddrAndDataDetects)
