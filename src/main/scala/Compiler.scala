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
          val deps = w.name.init.split('[').toSeq.map(_.replaceFirst(""".as_single_word\(\)""",""))
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
    result map grabMemAddr
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

  def predeclareBigSigs(hyperEdges: Seq[HyperedgeDep]) = {
    val bigSigs = hyperEdges filter { he: HyperedgeDep => { he.stmt match {
      case d: DefNode =>  bitWidth(d.value.tpe) > 64
      case c: Connect => {
        if (bitWidth(c.loc.tpe) > 64) {
          firrtl.Utils.kind(c.loc) match {
            case firrtl.WireKind => true
            case firrtl.PortKind => he.name.contains("$")
            case firrtl.InstanceKind => !he.name.contains(".")
            case _ => false
          }
        } else false
      }
    }}}
    bigSigs map { he => s"mpz_class ${he.name};" }
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
    // g.scoutZones(regNames)
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
      val nameToStmt = (bodyEdges map { he:HyperedgeDep => (he.name, he.stmt) }).toMap
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
      val topLevelHE = bodyEdges flatMap { he => {
        if (shadowedSigs.contains(he.name)) Seq()
        else {
          val deps = if (!trueShadows.contains(he.name)) he.deps
                     else he.deps ++ ((trueShadows(he.name) ++ falseShadows(he.name)) flatMap {
            name => heMap(name).deps
          })
          // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
          Seq(HyperedgeDep(he.name, deps.distinct, he.stmt))
        }
      }}
      // build graph on new hyperedges and run topo sort
      val reorderedNames = buildGraph(topLevelHE).reorderNames
      reorderedNames map nameToStmt map { stmt => {
        val emitted = emitStmt(doNotDec)(stmt)
        if (emitted.head.contains("?")) {
          val muxName = emitted.head.split("=").head.trim.split(" ").last
          if ((trueShadows(muxName).isEmpty) && (falseShadows(muxName).isEmpty))
            writeLines(indentLevel, emitted)
          else {
            val muxExpr = grabMux(stmt)
            // declare output type
            val resultTpe = findResultType(stmt)
            if ((!muxName.endsWith("$next")) && (!doNotDec.contains(muxName)))
              writeLines(indentLevel, s"${genCppType(resultTpe)} $muxName;")
            writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
            val trueHE = trueShadows(muxName) map { heMap(_) }
            writeBody(indentLevel + 1, trueHE, doNotShadow, doNotDec)
            writeLines(indentLevel + 1, s"$muxName = ${emitExpr(muxExpr.tval)};")
            writeLines(indentLevel, "} else {")
            val falseHE = falseShadows(muxName) map { heMap(_) }
            writeBody(indentLevel + 1, falseHE, doNotShadow, doNotDec)
            writeLines(indentLevel + 1, s"$muxName = ${emitExpr(muxExpr.fval)};")
            writeLines(indentLevel, "}")
          }
        } else writeLines(indentLevel, emitted)
      }}
    }
  }

  def genFlagName(regName: String) = s"ZONE_$regName".replace('.','$')

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

  def writeBodyWithZonesML(bodyEdges: Seq[HyperedgeDep], regNames: Seq[String],
                           allRegUpdates: Seq[String], resetTree: Seq[String],
                           topName: String, otherDeps: Seq[String],
                           doNotShadow: Seq[String]) {
    val trackActivity = false
    // map of name -> original hyperedge
    val heMap = (bodyEdges map { he => (he.name, he) }).toMap
    val regNamesSet = regNames.toSet

    // calculate zones based on all edges
    val g = buildGraph(bodyEdges)
    val zoneMapWithSources = g.findZonesML(regNames, doNotShadow)
    val zoneMap = zoneMapWithSources filter { _._1 != "ZONE_SOURCE" }
    g.analyzeZoningQuality(zoneMap)
    val inputsToZones = zoneMap.flatMap(_._2.inputs).toSet
    val nodesInZones = zoneMap.flatMap(_._2.members).toSet
    val nodesInZonesWithSources = zoneMapWithSources.flatMap(_._2.members).toSet
    val outputsFromZones = zoneMap.flatMap(_._2.outputs).toSet.diff(regNamesSet)

    // predeclare output nodes
    val outputTypes = outputsFromZones.toSeq map {name => findResultType(heMap(name).stmt)}
    val outputPairs = (outputTypes zip outputsFromZones).toSeq
    val preDecs = outputPairs map {case (tpe, name) => s"${genCppType(tpe)} $name;"}
    writeLines(0, preDecs)
    val doNotDec = outputsFromZones.toSet
    println(s"Output nodes: ${outputsFromZones.size}")

    // start emitting eval function
    writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    writeLines(1, resetTree)
    // predeclare zone activity flags
    val inputActivityFlags = inputsToZones map genFlagName
    writeLines(1, (inputActivityFlags map { flagName => s"bool $flagName = reset;"}).toSeq)
    println(s"Activity flags: ${inputsToZones.size}")

    // emit update checks for registers
    val regUpdateChecks = regNamesSet intersect inputsToZones map {
      regName => s"if ($regName != $regName$$next) ${genFlagName(regName)} = true;"
    }
    writeLines(1, regUpdateChecks.toSeq)

    // emit reg updates
    if (!allRegUpdates.isEmpty || trackActivity) {
      writeLines(1, "if (update_registers) {")
      writeLines(2, allRegUpdates)
      writeLines(1, "}")
    }

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

    // emit zone of sources
    if (zoneMapWithSources.contains("ZONE_SOURCE")) {
      val sourceZoneInfo = zoneMapWithSources("ZONE_SOURCE")
      val sourceZoneEdges = sourceZoneInfo.members map heMap
      writeBody(1, sourceZoneEdges, doNotShadow ++ doNotDec ++ sourceZoneInfo.outputs, doNotDec)
    }

    // emit each zone
    zonesReordered map zoneMap foreach { case Graph.ZoneInfo(inputs, members, outputs) => {
      val sensitivityListStr = inputs map genFlagName mkString(" || ")
      if (sensitivityListStr.isEmpty)
        writeLines(1, s"{")
      else
        writeLines(1, s"if ($sensitivityListStr) {")
      val outputsCleaned = (outputs.toSet intersect inputsToZones diff regNamesSet).toSeq
      val outputTypes = outputsCleaned map {name => findResultType(heMap(name).stmt)}
      val oldOutputs = outputsCleaned zip outputTypes map {case (name, tpe) => {
        s"${genCppType(tpe)} $name$$old = $name;"
      }}
      writeLines(2, oldOutputs)
      val zoneEdges = (members.toSet diff regNamesSet).toSeq map heMap
      writeBody(2, zoneEdges, doNotShadow ++ doNotDec, doNotDec)
      val outputChangeDetections = outputsCleaned map {
        name => s"${genFlagName(name)} |= $name != $name$$old;"
      }
      writeLines(2, outputChangeDetections)
      writeLines(1, "}")
    }}

    // emit rest of body (without redeclaring)
    writeBody(1, nonZoneEdges, doNotShadow, doNotDec)
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
    val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
    val allInstances = Seq((topModule.name, "")) ++
      findAllModuleInstances("", circuit)(topModule.body)
    val module_results = allInstances map {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => emitBody(m, circuit, prefix)
        case em: ExtModule => (Seq(), EmptyStmt, Seq())
      }
    }
    val resetTree = buildResetTree(allInstances)
    val (allRegUpdates, allBodies, allMemUpdates) = module_results.unzip3
    val allDeps = allBodies flatMap findDependencesStmt
    val (otherDeps, prints, stops) = separatePrintsAndStops(allDeps)
    val regNames = allRegUpdates.flatten map { _.split("=").head.trim }
    val memDeps = (allMemUpdates.flatten) flatMap findDependencesMemWrite
    val pAndSDeps = (prints ++ stops) flatMap { he => he.deps }
    writeLines(0, "")
    // decRegActivityTracking(regNames)
    // writeLines(0, "")
    // start emitting eval function
    // writeLines(0, s"void $topName::eval(bool update_registers, bool verbose, bool done_reset) {")
    // writeLines(1, resetTree)
    // emit reg updates
    // if (!allRegUpdates.flatten.isEmpty) {
    //   writeLines(1, "if (update_registers) {")
    //   recRegActivityTracking(regNames)
    //   writeLines(2, allRegUpdates.flatten)
    //   writeLines(1, "}")
    // }
    writeBodyWithZonesML(otherDeps, regNames, allRegUpdates.flatten, resetTree,
                         topName, memDeps ++ pAndSDeps, (regNames ++ memDeps ++ pAndSDeps).distinct)
    // writeBody(1, otherDeps, (regNames ++ memDeps ++ pAndSDeps).distinct, regNames.toSet)
    // writeBodySimple(1, otherDeps, regNames)
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
    writeLines(1, allMemUpdates.flatten)
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
    passes.RemoveValidIf,
    passes.ConstProp,
    passes.PadWidths,
    passes.ConstProp,
    passes.Legalize,
    passes.VerilogWrap,
    passes.memlib.VerilogMemDelays,
    passes.ConstProp,
    passes.SplitExpressions,
    passes.CommonSubexpressionElimination,
    passes.DeadCodeElimination,
    passes.RemoveEmpty,
    InferAddw,
    WireConstProp,
    ZeroFromBits,
    WireConstProp,
    RandInitInvalids,
    NoResetsOrClockConnects)
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
