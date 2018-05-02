package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._


object NoClockConnects extends Pass {
  def desc = "Removes Connects or DefNodes to anything that is ClockType"
  // FUTURE: remove this pass and properly support multi-clock

  def cutConnectsStmt(s: Statement): Statement = {
    val noConnects = s match {
      case c: Connect if (c.expr.tpe == ClockType || c.loc.tpe == ClockType) => EmptyStmt
      case d: DefNode if (d.value.tpe == ClockType) => EmptyStmt
      case _ => s
    }
    noConnects map cutConnectsStmt
  }

  def noConnectsModule(m: Module): Module = {
    Module(m.info, m.name, m.ports, squashEmpty(cutConnectsStmt(m.body)))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => noConnectsModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
