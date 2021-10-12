package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.Mappers._
import firrtl.passes._
import firrtl.PrimOps.AsAsyncReset


object RemoveAsAsyncReset extends Pass {
  def desc = "Removes AsAsyncReset expressions since async indistinguishable with cycle-level timing"
  //  TODO: remove when multiple clocks supported

  override def prerequisites = Seq(Dependency(ReplaceAsyncRegs), Dependency(RegFromMem1))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform): Boolean = a match {
    case firrtl.transforms.RemoveReset => true
    case _                             => false
  }

  def removeAsyncResetExpr(e: Expression): Expression = {
      val replaced = e match {
        case p @ DoPrim(AsAsyncReset, _, _, _) => p.args.head
        case _ => e
      }
      replaced map removeAsyncResetExpr
  }

  def removeAsyncResetStmt(s: Statement): Statement = s map removeAsyncResetStmt map removeAsyncResetExpr

  def removeAsyncTypes(s: Statement): Statement = {
    val replaced = s match {
      case d @ DefRegister(_, _, _, _, w @ WRef(_, AsyncResetType, _, _), _) => d.copy(reset = w.copy(tpe = ResetType))
      case _ => s
    }
    replaced map removeAsyncTypes
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => m.copy(body = m.body map removeAsyncResetStmt map removeAsyncTypes)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
