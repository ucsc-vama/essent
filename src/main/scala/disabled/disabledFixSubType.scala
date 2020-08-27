package disabled

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.Mappers._
import firrtl.options.PreservesAll
import firrtl.passes._
import firrtl.Utils._


object FixSubType extends Pass with DependencyAPIMigration with PreservesAll[Transform] {
  def desc = "Inserts asUInt onto sub of two UInts (should otherwise be an SInt)"
  // due to poorly specified change (firrtl commit ebb471bd3c22e092e5c2ce55284abe8c13b25662)
  // FUTURE: consider change firrtl-sig if this change is permanent

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized

  def allUIntType(p: DoPrim): Boolean = {
    p.tpe.isInstanceOf[UIntType] &&
    p.args(0).tpe.isInstanceOf[UIntType] &&
    p.args(1).tpe.isInstanceOf[UIntType]
  }

  def convUIntSubExpr(e: Expression): Expression = {
    val replaced = e match {
      case p @ DoPrim(Sub, _, _, _) if (allUIntType(p)) => {
        val typeSwitched = p.tpe match {
          case UIntType(IntWidth(w)) => SIntType(IntWidth(w))
        }
        val subWithTypeReplaced = p.copy(tpe = typeSwitched)
        DoPrim(AsUInt, Seq(subWithTypeReplaced), Seq(), p.tpe)
      }
      case _ => e
    }
    replaced map convUIntSubExpr
  }

  def convUIntSubStmt(s: Statement): Statement = s map convUIntSubStmt map convUIntSubExpr

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => m.copy(body = m.body map convUIntSubStmt)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
