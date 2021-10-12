package essent.passes

import essent.Emitter._
import essent.ir._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.options.Dependency
import firrtl.passes._
import firrtl.Utils._


object SplitRegUpdates extends Pass {
  def desc = "Appends $next to the name of any reg being assigned to"

  override def prerequisites = Seq(Dependency(essent.passes.RegFromMem1), Dependency(essent.passes.ReplaceAsyncRegs) , Dependency(essent.passes.ReplaceRsvdKeywords))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def renameRegStmt(s: Statement): Statement = {
    val replaced = s match {
      case c: Connect if (firrtl.Utils.kind(c.loc) == firrtl.RegKind) => {
        DefNode(c.info, emitExpr(c.loc) + "$next", c.expr)
      }
      case _ => s
    }
    replaced map renameRegStmt
  }

  // FUTURE: what if reg is dead? should update be generated for connect?
  def generateRegUpdates(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts flatMap generateRegUpdates
    case r: DefRegister => {
      Seq(RegUpdate(NoInfo, WRef(r.name, r.tpe, RegKind), WRef(r.name + "$next", r.tpe, RegKind)))
    }
    case _ => Seq()
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => {
        val newBody = squashEmpty(Block(Seq(renameRegStmt(m.body)) ++ generateRegUpdates(m.body)))
        m.copy(body = newBody)
      }
    }
    Circuit(c.info, modulesx, c.main)
  }
}
