package disabled

import essent.Emitter._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._

import scala.math.BigInt
import scala.util.Random


object RandInitInvalids extends Pass {
  def desc = "Randomly initialize invalid signals"

  def genRandomLiteral(width: Int): BigInt = BigInt(width, Random)

  def randInitStmt(portNames: Set[String])(s: Statement): Statement = {
    val replaced = s match {
      case i: IsInvalid => {
        val randLit = i.expr.tpe match {
          case UIntType(IntWidth(w)) => UIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
          case SIntType(IntWidth(w)) => SIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
        }
        if (portNames.contains(emitExpr(i.expr)))
          Connect(i.info, i.expr, randLit)
        else
          DefNode(i.info, emitExpr(i.expr), randLit)
      }
      case _ => s
    }
    replaced map randInitStmt(portNames)
  }

  def randInitModule(m: Module): Module = {
    val portNames = (m.ports map { _.name }).toSet
    Module(m.info, m.name, m.ports, squashEmpty(randInitStmt(portNames)(m.body)))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => randInitModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
