package disabled

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.PrimOps._


object ZeroFromBits extends Pass {
  def desc = "Replaces bit extracts on literal zeros with zeros"

  def simpBitsExpr(e: Expression): Expression = {
    val bigZero = BigInt(0)
    val replaced = e match {
      case p: DoPrim => p.op match {
        case Bits => p.args.head match {
          case UIntLiteral(bigZero, _) => UIntLiteral(bigZero, IntWidth(bitWidth(p.tpe)))
          case _ => p
        }
        case _ => p
      }
      case _ => e
    }
    replaced map simpBitsExpr
  }

  def simpBitsStmt(s: Statement): Statement = {
    s map simpBitsStmt map simpBitsExpr
  }

  def simpBitsModule(m: Module): Module = {
    Module(m.info, m.name, m.ports, simpBitsStmt(m.body))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => simpBitsModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
