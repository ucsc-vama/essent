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
  case class HyperedgeDep(name: String, deps: Seq[String], stmt: Statement)

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
    val (prints, stops) = stopAndPrints.map {dep => dep.stmt}.partition { _ match {
      case p: Print => true
      case _ => false
    }}
    (otherDeps, prints ++ stops)
  }

  def buildGraph(hyperEdges: Seq[HyperedgeDep]) = {
    val g = new Graph
    hyperEdges foreach { he:HyperedgeDep =>
      g.addNodeWithDeps(he.name, he.deps, emitStmt(he.stmt).head)
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
    writeLines(1, m.ports flatMap emitPort)
    writeLines(1, moduleDecs)
    writeLines(0, "")
    writeLines(1, s"$modName() {")
    writeLines(2, initializeVals(m, registers, memories))
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
    writeLines(1, m.ports flatMap emitPort)
    writeLines(0, s"} $modName;")
  }


  def buildEval(circuit: Circuit) = {
    val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
    val allInstances = Seq((topModule.name, "")) ++
      findAllModuleInstances("", circuit)(topModule.body)
    val module_results = allInstances map {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => emitBody(m.body, prefix)
        case em: ExtModule => (Seq(), EmptyStmt, Seq())
      }
    }
    val (allRegUpdates, allBodies, allMemUpdates) = module_results.unzip3
    val allDeps = allBodies flatMap findDependencesStmt
    val (otherDeps, printsAndStops) = separatePrintsAndStops(allDeps)
    val reorderedBodies = buildGraph(otherDeps).reorderCommands
    allRegUpdates.flatten ++ reorderedBodies ++
    (printsAndStops flatMap emitStmt) ++ allMemUpdates.flatten
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
    writeLines(0, s"void $topName::eval(bool update_registers) {")
    writeLines(1, buildEval(circuit))
    writeLines(0, "}")
    writeLines(0, "")
    writeLines(0, s"void $topName::connect_harness(CommWrapper<struct $topName> *comm) {")
    writeLines(1, HarnessGenerator.harnessConnections(topModule))
    writeLines(0, "}")
    writeLines(0, "")
    writeLines(0, s"#endif  // $headerGuardName")
    println(circuit.serialize)
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



class CCCompiler extends Compiler {
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
  )
}
