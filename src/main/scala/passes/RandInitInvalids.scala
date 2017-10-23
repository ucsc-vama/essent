package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._

import scala.math.BigInt
import scala.util.Random


object RandInitInvalids extends Pass {
  def name = "Randomly initialize invalid signals"

  def genRandomLiteral(width: Int): BigInt = BigInt(width, Random)

  def randInitStmt(s: Statement): Statement = {
    val replaced = s match {
      case i: IsInvalid => {
        val randLit = i.expr.tpe match {
          case UIntType(IntWidth(w)) => UIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
          case SIntType(IntWidth(w)) => SIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
        }
        Connect(i.info, i.expr, randLit)
      }
      case _ => s
    }
    replaced map randInitStmt
  }

  def randInitModule(m: Module): Module = {
    Module(m.info, m.name, m.ports, squashEmpty(randInitStmt(m.body)))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => randInitModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
