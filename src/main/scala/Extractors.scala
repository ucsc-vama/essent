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
    case m: Module => m.ports.map{_.name}.filter{s => s != "clock"}
    case em: ExtModule => Seq()
  }

  def findModuleInstances(s: Statement): Seq[(String,String)] = s match {
    case b: Block => b.stmts flatMap findModuleInstances
    case i: WDefInstance => Seq((i.module, i.name))
    case _ => Seq()
  }

  def findAllModuleInstances(circuit: Circuit): Seq[(String,String)] = {
    def crawlModuleInstances(prefix: String, circuit: Circuit)(s: Statement): Seq[(String,String)] = {
      s match {
        case b: Block => b.stmts flatMap crawlModuleInstances(prefix, circuit)
        case i: WDefInstance => {
          val nestedModules = findModule(i.module, circuit) match {
            case m: Module => crawlModuleInstances(s"$prefix${i.name}.", circuit)(m.body)
            case em: ExtModule => Seq()
          }
          Seq((i.module, s"$prefix${i.name}.")) ++ nestedModules
        }
        case _ => Seq()
      }
    }
    val topModule = findModule(circuit.main, circuit) match {case m: Module => m}
    Seq((circuit.main, "")) ++ crawlModuleInstances("", circuit)(topModule.body)
  }

  def findModule(name: String, circuit: Circuit) =
    circuit.modules.find(_.name == name).get

  def partitionByType[T <: Statement](stmts: Seq[Statement])(implicit tag: ClassTag[T]): (Seq[T], Seq[Statement]) = {
    def filterOutType(s: Statement): Seq[Statement] = s match {
      case t: T => Seq[Statement]()
      case b: Block => b.stmts flatMap filterOutType
      case _ => Seq(s)
    }
    (stmts flatMap findInstancesOf[T], stmts flatMap filterOutType)
  }

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

  def findResultName(stmt: Statement): Option[String] = stmt match {
    case d: DefNode => Some(d.name)
    case c: Connect => Some(emitExpr(c.loc))
    case ms: MuxShadowed => Some(ms.name)
    case ru: RegUpdate => Some(emitExpr(ru.regRef))
    case mw: MemWrite => Some(mw.memName)
    case p: Print => None
    case s: Stop => None
    case _ => throw new Exception(s"Don't know how to find result name of ${stmt.serialize}")
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
    case r: DefRegister => r.tpe
    case m: DefMemory => m.dataType
    case _ => throw new Exception("not a connect or defnode")
  }

  // Graph dependency building
  def findDependencesExpr(e: Expression): Seq[String] = {
    val result = e match {
      case w: WRef => Seq(w.name)
      case m: Mux => Seq(m.cond, m.tval, m.fval) flatMap findDependencesExpr
      case w: WSubField => {
        val innerResult = findDependencesExpr(w.expr)
        if (innerResult.isEmpty) Seq()
        else Seq(s"${innerResult.head}.${w.name}")
      }
      case w: WSubAccess => Seq(w.expr, w.index) flatMap findDependencesExpr
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
    case c: Connect => Seq(HyperedgeDep(emitExpr(c.loc), findDependencesExpr(c.expr), s))
    case ru: RegUpdate => Seq(HyperedgeDep(emitExpr(ru.regRef)+"$final", findDependencesExpr(ru.expr), s))
    case mw: MemWrite => {
      val deps = Seq(mw.wrEn, mw.wrMask, mw.wrAddr, mw.wrData) flatMap findDependencesExpr
      Seq(HyperedgeDep(mw.nodeName, deps.distinct, s))
    }
    case p: Print => {
      val deps = (Seq(p.en) ++ p.args) flatMap findDependencesExpr
      val uniqueName = "PRINTF" + emitExpr(p.clk) + deps.mkString("$") + Util.tidyString(p.string.serialize)
      // FUTURE: more efficient unique name (perhaps line number?)
      Seq(HyperedgeDep(uniqueName, deps.distinct, p))
    }
    case st: Stop => {
      val deps = findDependencesExpr(st.en)
      val uniqueName = "STOP" + emitExpr(st.clk) + deps.mkString("$") + st.ret
      // FUTURE: more unique name (perhaps line number?)
      Seq(HyperedgeDep(uniqueName, deps, st))
    }
    case r: DefRegister => Seq(HyperedgeDep(r.name, Seq(), r))
    case w: DefWire => Seq()
    case m: DefMemory => Seq(HyperedgeDep(m.name, Seq(), m))
    case i: WDefInstance => Seq()
    case EmptyStmt => Seq()
    case _ => throw new Exception(s"unexpected statement type! $s")
  }

  def flattenStmts(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts flatMap flattenStmts
    case az: ActivityZone => az.memberStmts flatMap flattenStmts
    case m: MuxShadowed => (m.tShadow ++ m.fShadow) flatMap flattenStmts
    case EmptyStmt => Seq()
    case _ => Seq(s)
  }

  def flattenModuleBody(m: Module, prefix: String, circuit: Circuit) = {
    val body = addPrefixToNameStmt(prefix)(m.body)
    val nodeNames = findNodes(body) map { _.name }
    val wireNames = findWires(body) map { _.name }
    val externalPortNames = findPortNames(m) map { prefix + _ }
    val internalPortNames = findModuleInstances(m.body) flatMap {
      case (moduleType, moduleName) =>
        findPortNames(findModule(moduleType, circuit)) map {prefix + s"$moduleName." + _}
    }
    val allTempSigs = nodeNames ++ wireNames ++ externalPortNames ++ internalPortNames
    val renames = (allTempSigs filter { _.contains('.') } map { s => (s, s.replace('.','$'))}).toMap
    replaceNamesStmt(renames)(body)
  }

  def findExternalPorts(circuit: Circuit): Map[String,Type] = {
    val allInstances = findAllModuleInstances(circuit)
    val extIOs = allInstances flatMap {
      case (modName, prefix) => findModule(modName, circuit) match {
        case m: Module => {
          if (m.name == circuit.main) m.ports map { port => (s"$prefix${port.name}", port.tpe) }
          else None
        }
        case em: ExtModule => em.ports map { port => (s"$prefix${port.name}", port.tpe) }
      }
    }
    extIOs.toMap
  }
}
