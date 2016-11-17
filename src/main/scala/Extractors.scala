package essent

import essent.Emitter._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._


// Find methods
// assumption: registers can only appear in blocks since whens expanded

object Extract {
  def findRegisters(s: Statement): Seq[DefRegister] = s match {
    case b: Block => b.stmts flatMap findRegisters
    case d: DefRegister => Seq(d)
    case _ => Seq()
  }

  def findWires(s: Statement): Seq[DefWire] = s match {
    case b: Block => b.stmts flatMap findWires
    case d: DefWire => Seq(d)
    case _ => Seq()
  }

  def findMemory(s: Statement): Seq[DefMemory] = s match {
    case b: Block => b.stmts flatMap findMemory
    case d: DefMemory => Seq(d)
    case _ => Seq()
  }

  def findNodes(s: Statement): Seq[DefNode] = s match {
    case b: Block => b.stmts flatMap findNodes
    case d: DefNode => Seq(d)
    case _ => Seq()
  }

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
}
