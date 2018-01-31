package essent

import essent.Emitter._
import essent.ir._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._

import scala.reflect.ClassTag

// Find methods
// assumption: registers can only appear in blocks since whens expanded

object Extract {
  // https://medium.com/@sinisalouc/overcoming-type-erasure-in-scala-8f2422070d20
  def findInstancesOf[T <: Statement](s: Statement)(implicit tag: ClassTag[T]): Seq[T] = s match {
    case t: T => Seq(t)
    case b: Block => b.stmts flatMap findInstancesOf[T]
    case _ => Seq()
  }

  def findRegisters(s: Statement) = findInstancesOf[DefRegister](s)

  def findWires(s: Statement) = findInstancesOf[DefWire](s)

  def findMemory(s: Statement) = findInstancesOf[DefMemory](s)

  def findNodes(s: Statement) = findInstancesOf[DefNode](s)

  def findPortNames(dm: DefModule): Seq[String] = dm match {
    case m: Module => m.ports.map{_.name}.filter{s => s != "clock" && s != "reset"}
    case em: ExtModule => Seq()
  }

  def findModuleInstances(s: Statement): Seq[(String,String)] = s match {
    case b: Block => b.stmts flatMap findModuleInstances
    case i: WDefInstance => Seq((i.module, i.name))
    case _ => Seq()
  }

  def findAllModuleInstances(prefix: String, circuit: Circuit)(s: Statement): Seq[(String,String)] =
    s match {
      case b: Block => b.stmts flatMap findAllModuleInstances(prefix, circuit)
      case i: WDefInstance => {
        val nestedModules = findModule(i.module, circuit) match {
          case m: Module => findAllModuleInstances(s"$prefix${i.name}.", circuit)(m.body)
          case em: ExtModule => Seq()
        }
        Seq((i.module, s"$prefix${i.name}.")) ++ nestedModules
      }
      case _ => Seq()
    }

  def findModule(name: String, circuit: Circuit) =
    circuit.modules.find(_.name == name).get

  def grabMux(stmt: Statement) = stmt match {
    case DefNode(_, _, m: Mux) => m
    case Connect(_, _, m: Mux) => m
    case _ => throw new Exception("not an defnode or connect")
  }

  def findMuxOutputNames(hyperEdges: Seq[HyperedgeDep]) = hyperEdges flatMap {
    he: HyperedgeDep => he.stmt match {
      case DefNode(_, _, Mux(_, _, _, _)) => Seq(he.name)
      case Connect(_, _, Mux(_, _, _, _)) => Seq(he.name)
      case _ => Seq()
    }
  }

  def findResultName(stmt: Statement): String = stmt match {
    case d: DefNode => d.name
    case c: Connect => emitExpr(c.loc)
    case ms: MuxShadowed => ms.name
    case _ => throw new Exception("Don't know how to find result name")
  }

  def findMuxExpr(hyperEdges: Seq[HyperedgeDep]) = hyperEdges flatMap {
    he: HyperedgeDep => he.stmt match {
      case DefNode(_, _, muxExpr: Mux) => Seq((he.name, muxExpr))
      case Connect(_, _, muxExpr: Mux) => Seq((he.name, muxExpr))
      case _ => Seq()
    }
  }

  def findResultType(stmt: Statement) = stmt match {
    case d: DefNode => d.value.tpe
    case c: Connect => c.loc.tpe
    case _ => throw new Exception("not a connect or defnode")
  }

  // Graph dependency building
  def findDependencesExpr(e: Expression): Seq[String] = {
    val result = e match {
      case w: WRef => Seq(w.name)
      case m: Mux => Seq(m.cond, m.tval, m.fval) flatMap findDependencesExpr
      case w: WSubField => Seq(emitExpr(w))
      case w: WSubAccess => Seq(emitExpr(w.expr), emitExpr(w.index))
      case p: DoPrim => p.args flatMap findDependencesExpr
      case u: UIntLiteral => Seq()
      case s: SIntLiteral => Seq()
      case _ => throw new Exception("unexpected expression type! " + e)
    }
    result.distinct
  }

  def findDependencesStmt(s: Statement): Seq[HyperedgeDep] = s match {
    case b: Block => b.stmts flatMap findDependencesStmt
    case d: DefNode => Seq(HyperedgeDep(d.name, findDependencesExpr(d.value), s))
    case c: Connect => {
      val name = emitExpr(c.loc)
      val deps = findDependencesExpr(c.expr)
      firrtl.Utils.kind(c.loc) match {
        case firrtl.MemKind => Seq()
        case _ => Seq(HyperedgeDep(name, deps, s))
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

  def findDependencesMemWrite(mu: MemUpdate): Seq[String] = {
    val deps = Seq(mu.wrEnName, mu.wrMaskName, mu.wrAddrName, mu.wrDataName)
    (deps filter { name => !name.startsWith("UInt<1>(0x") }).distinct
  }
}
