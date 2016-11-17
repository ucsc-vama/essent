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

  def separatePrintsAndStops(deps: Seq[HyperedgeDep]) = {
    val (stopAndPrints, otherDeps) = deps.partition { dep => dep.stmt match {
      case s: Stop => true
      case p: Print => true
      case _ => false
    }}
    (otherDeps, stopAndPrints.map {dep => dep.stmt})
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

  def emitBodyWithShadows(hyperEdges: Seq[HyperedgeDep], regNames: Seq[String]) {
    val muxOutputNames = findMuxOutputNames(hyperEdges)
    val shadowG = new Graph
    hyperEdges foreach { he:HyperedgeDep =>
      shadowG.addNodeWithDeps(he.name, he.deps, he.stmt)
    }
    val shadows = shadowG.findAllShadows(muxOutputNames, regNames)
    // map of muxName -> true shadows, map of muxName -> false shadows
    val trueMap = (shadows map {case (muxName, tShadow, fShadow) => (muxName, tShadow)}).toMap
    val falseMap = (shadows map {case (muxName, tShadow, fShadow) => (muxName, fShadow)}).toMap
    // map of signals in shadows -> muxName
    val muxMap = (shadows flatMap {
      case (muxName, tShadow, fShadow) => (tShadow ++ fShadow) map { (_, muxName) }
    }).toMap
    // map of name -> original deps
    val depMap = (hyperEdges map { he => (he.name, he.deps) }).toMap
    // flatmap hyperedges, make mux depend on all of its shadows' dependences
    //   - also make all that depend on item in shadow depend on mux
    val combinedHEdges = hyperEdges flatMap { he => {
      if (muxMap.contains(he.name)) Seq()
      else {
        val deps = if (trueMap.contains(he.name)) {
          val muxExpr = grabMux(he.stmt)
          he.deps ++ ((trueMap(he.name) ++ falseMap(he.name)) flatMap { name => depMap(name)})
        } else he.deps
        // assuming can't depend on internal of other mux cluster, o/w wouldn't be shadow
        Seq(HyperedgeDep(he.name, deps.distinct, he.stmt))
      }
    }}
    // build graph on new hyperedges and run topo sort
    val topGraph = new Graph
    combinedHEdges foreach { he:HyperedgeDep =>
      topGraph.addNodeWithDeps(he.name, he.deps, he.stmt)
    }
    val reorderedStmts = topGraph.reorderCommands
    // map of name -> original hyperedge
    val heMap = (hyperEdges map { he => (he.name, he) }).toMap
    // be careful when emitting, if mux look up shadows
    //   - build if block (with predeclared output type)
    //   - for each shadow, build graph and run topo sort
    reorderedStmts map { stmt => {
      val emitted = emitStmt(stmt)
      if (emitted.head.contains("?")) {
        val muxName = emitted.head.split("=").head.trim.split(" ").last
        val muxExpr = grabMux(stmt)
        // declare output type - don't redeclare big sigs
        val resultTpe = stmt match {
          case d: DefNode => d.value.tpe
          case c: Connect => c.loc.tpe
          case _ => throw new Exception("Mux not in connect or defnode")
        }
        if ((bitWidth(resultTpe) <= 64) && (!muxName.endsWith("$next")))
          writeLines(1, s"${genCppType(resultTpe)} $muxName;")
        // if (mux cond)
        writeLines(1, s"if (${emitExpr(muxExpr.cond)}) {")
        // build true case and topo sort
        val trueGraph = new Graph
        val trueHE = trueMap(muxName) map { heMap(_) }
        trueHE foreach {he => trueGraph.addNodeWithDeps(he.name, he.deps, he.stmt)}
        writeLines(2, trueGraph.reorderCommands flatMap emitStmt)
        // assign mux var
        writeLines(2, s"$muxName = ${emitExpr(muxExpr.tval)};")
        // else
        writeLines(1, "} else {")
        // build false case and topo sort
        val falseGraph = new Graph
        val falseHE = falseMap(muxName) map { heMap(_) }
        falseHE foreach {he => falseGraph.addNodeWithDeps(he.name, he.deps, he.stmt)}
        writeLines(2, falseGraph.reorderCommands flatMap emitStmt)
        // assign mux var
        writeLines(2, s"$muxName = ${emitExpr(muxExpr.fval)};")
        writeLines(1, "}")
      } else writeLines(1, emitted)
    }}
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
    val reorderedBodies = buildGraph(otherDeps).reorderCommands
    // val totalSingleAssigns = reorderedBodies.filter{
    //   s => s.contains("=") && (s.split("=").last.trim.count(_ == ' ') == 0)
    // }.size
    // println(s"Assigns: $totalSingleAssigns / ${reorderedBodies.size} (single/all)")
    val regNames = allRegUpdates.flatten map { _.split("=").head.trim }
    writeLines(0, bigDecs)
    writeLines(0, "")
    writeLines(0, s"void $topName::eval(bool update_registers) {")
    writeLines(1, resetTree)
    writeLines(1, "if (update_registers) {")
    writeLines(2, allRegUpdates.flatten)
    writeLines(1, "}")
    emitBodyWithShadows(otherDeps, regNames)
    writeLines(1, emitPrintsAndStops(printsAndStops))
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
