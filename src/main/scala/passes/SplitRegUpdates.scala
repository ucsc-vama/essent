package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._


object SplitRegUpdates extends Pass {
  def desc = "Appends $next to the name of any reg being assigned to"
  // Assumes registers are assigned to via Connect (and not DefNode)

  def renameRegStmt(s: Statement): Statement = {
    val replaced = s match {
      case c: Connect => {
        firrtl.Utils.kind(c.loc) match {
          case firrtl.RegKind => { 
            val newLoc = c.loc match {
              case w: WRef => w.copy(name = w.name + "$next")
              case w: WSubField => w.copy(name = w.name + "$next")
              case _ => c.loc
            }
            c.copy(loc = newLoc)
          }
          case _ => c
        }
      }
      case _ => s
    }
    replaced map renameRegStmt
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => m.copy(body = renameRegStmt(m.body))
    }
    Circuit(c.info, modulesx, c.main)
  }
}
