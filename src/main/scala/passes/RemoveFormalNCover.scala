package essent.passes

import firrtl.Mappers._
import firrtl._
import firrtl.ir._
import firrtl.passes._


object RemoveFormalNCover extends Pass {
  def desc = "Removes FIRRTL formal and coverage (Assume, Cover) as they are not supported by ESSENT"

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = Seq.empty
  override def optionalPrerequisiteOf = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def removeUnsupported(s: Statement): Statement = s.map(removeUnsupported) match {
    case Block(stmts) =>
      val newStmts = stmts.filter{_ match {
        case s: Verification => s.op match{
          case Formal.Cover => false
          case Formal.Assume => false
          case _ => true
        }
        case _ => true
      }}
      newStmts.size match {
        case 0 => EmptyStmt
        case 1 => newStmts.head
        case _ => Block(newStmts)
      }
    case sx => sx
  }

  private def onModule(m: DefModule): DefModule = {
    m match {
      case m: Module    => Module(m.info, m.name, m.ports, removeUnsupported(m.body))
      case m: ExtModule => m
    }
  }
  def run(c: Circuit): Circuit = Circuit(c.info, c.modules.map(onModule), c.main)
}
