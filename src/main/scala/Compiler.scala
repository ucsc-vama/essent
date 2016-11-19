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
      case w: WRef => Seq(w.name)
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
    val insideIf = "([(].*[)])".r.findAllIn(emittedCmd).toList.head.tail.init
    val enAndMask = insideIf.split(" && ")
    val memAndAddr = emittedCmd.split("=").head.trim.split(" ").last.init.split('[')
    val dataName = emittedCmd.split("=").last.trim.init
    val deps = enAndMask.toSeq ++ memAndAddr.toSeq ++ Seq(dataName)
    deps filter { name: String => !name.startsWith("0x") }
  }

  def separatePrintsAndStops(deps: Seq[HyperedgeDep]) = {
    val (stopAndPrints, otherDeps) = deps.partition { dep => dep.stmt match {
      case s: Stop => true
      case p: Print => true
      case _ => false
    }}
    (otherDeps, stopAndPrints)
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
      g.addNodeWithDeps(he.name, he.deps, he.stmt)
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
      writeLines(1, "void eval(bool update_registers);")
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
    val reorderedConnects = buildGraph(allDeps).reorderCommands
    reorderedConnects flatMap emitStmt
  }

  def writeBody(indentLevel: Int, bodyEdges: Seq[HyperedgeDep], doNotShadow: Seq[String]) {
    if (!bodyEdges.isEmpty) {
      val muxOutputNames = findMuxOutputNames(bodyEdges)
      val shadows = buildGraph(bodyEdges).findAllShadows(muxOutputNames, doNotShadow)
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
      val reorderedStmts = buildGraph(topLevelHE).reorderCommands
      reorderedStmts map { stmt => {
        val emitted = emitStmt(stmt)
        if (emitted.head.contains("?")) {
          val muxName = emitted.head.split("=").head.trim.split(" ").last
          if ((trueShadows(muxName).isEmpty) && (falseShadows(muxName).isEmpty))
            writeLines(indentLevel, emitted)
          else {
            val muxExpr = grabMux(stmt)
            // declare output type - don't redeclare big sigs
            val resultTpe = findResultType(stmt)
            if ((bitWidth(resultTpe) <= 64) && (!muxName.endsWith("$next")))
              writeLines(indentLevel, s"${genCppType(resultTpe)} $muxName;")
            writeLines(indentLevel, s"if (${emitExpr(muxExpr.cond)}) {")
            val trueHE = trueShadows(muxName) map { heMap(_) }
            writeBody(indentLevel + 1, trueHE, doNotShadow)
            writeLines(indentLevel + 1, s"$muxName = ${emitExpr(muxExpr.tval)};")
            writeLines(indentLevel, "} else {")
            val falseHE = falseShadows(muxName) map { heMap(_) }
            writeBody(indentLevel + 1, falseHE, doNotShadow)
            writeLines(indentLevel + 1, s"$muxName = ${emitExpr(muxExpr.fval)};")
            writeLines(indentLevel, "}")
          }
        } else writeLines(indentLevel, emitted)
      }}
    }
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
    val (otherDeps, printsAndStops) = separatePrintsAndStops(allDeps)
    val bigDecs = predeclareBigSigs(otherDeps)
    val regNames = allRegUpdates.flatten map { _.split("=").head.trim }
    val memDeps = (allMemUpdates.flatten) flatMap findDependencesMemWrite
    val pAndSDeps = printsAndStops flatMap { he => he.deps }
    writeLines(0, bigDecs)
    writeLines(0, "")
    // writeLines(0, "uint64_t total_transitions = 0;")
    // writeLines(0, "uint64_t cycles_ticked = 0;")
    writeLines(0, s"void $topName::eval(bool update_registers) {")
    writeLines(1, resetTree)
    writeLines(1, "if (update_registers) {")
    // writeRegActivityTracking(regNames) // note doesn't consider resets
    writeLines(2, allRegUpdates.flatten)
    writeLines(1, "}")
    writeBody(1, otherDeps, (regNames ++ memDeps ++ pAndSDeps).distinct)
    writeLines(1, emitPrintsAndStops(printsAndStops.map {dep => dep.stmt}))
    writeLines(1, allMemUpdates.flatten)
    writeLines(0, "}")
  }


  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    writeLines(0, s"#ifndef $headerGuardName")
    writeLines(0, s"#define $headerGuardName")
    writeLines(0, "")
    writeLines(0, "#include <cstdint>")
    writeLines(0, "#include <cstdlib>")
    writeLines(0, "#include <gmpxx.h>")
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
