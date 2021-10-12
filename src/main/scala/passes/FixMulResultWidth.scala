package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.Mappers._
import firrtl.passes._


object FixMulResultWidth extends Pass {
  def desc = "Inserts tail operators on mul operators if result width is too small"
  // FUTURE: is this a bug in firrtl width inference?

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def mulTailExpr(e: Expression): Expression = {
    val replaced = e match {
      case p @ DoPrim(Mul, _, _, _) => {
        val correctWidth = bitWidth(p.args(0).tpe) + bitWidth(p.args(1).tpe)
        val correctResultType = p.tpe.mapWidth(_ => IntWidth(correctWidth))
        if (bitWidth(p.tpe) != bitWidth(correctResultType)) {
          val delta = bitWidth(correctResultType) - bitWidth(p.tpe)
          val newMul = p.copy(tpe = correctResultType)
          DoPrim(Tail, Seq(newMul), Seq(delta), p.tpe)
        } else e
      } 
      case _ => e
    }
    replaced map mulTailExpr
  }

  def mulTailStmt(s: Statement): Statement = s map mulTailStmt map mulTailExpr

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => m.copy(body = m.body map mulTailStmt)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
