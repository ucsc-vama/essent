package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._


object NoResetsOrClockConnects extends Pass {
  def name = "Removes connects to .clock or .reset"

  def cutConnectsStmt(s: Statement): Statement = {
    val noConnects = s match {
      case c: Connect => c.loc match {
        case w: WSubField => {
          if (w.name == "clock" || w.name == "reset" || w.name == "clk") EmptyStmt
          // if (w.name == "clock" || w.name == "clk") EmptyStmt
          else c
        }
        case _ => c
      }
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
