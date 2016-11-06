package essent

import essent.Extract._
import essent.Emitter._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.passes.bitWidth
import firrtl.Utils._

import scala.math.BigInt
import scala.util.Random


object RandInitInvalids extends Pass {
  def name = "Randomly initialize invalid signals"

  def genRandomLiteral(width: Int): BigInt = BigInt(width, Random)

  def randInitStmt(alreadyDeclared: Set[String])(s: Statement): Statement = {
    val replaced = s match {
      case i: IsInvalid => {
        val name = emitExpr(i.expr)
        val randLit = i.expr.tpe match {
          case UIntType(IntWidth(w)) => UIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
          case SIntType(IntWidth(w)) => SIntLiteral(genRandomLiteral(w.toInt), IntWidth(w))
        }
        if (alreadyDeclared.contains(name)) Connect(i.info, i.expr, randLit)
        else DefNode(i.info, name, randLit)
      }
      case _ => s
    }
    replaced map randInitStmt(alreadyDeclared)
  }

  def randInitModule(m: Module): Module = {
    val registerNames = findRegisters(m.body) map { _.name }
    val ioNames = m.ports map { _.name }
    val alreadyDeclared = (registerNames ++ ioNames).toSet
    val replacedStmts = randInitStmt(alreadyDeclared)(m.body)
    Module(m.info, m.name, m.ports, squashEmpty(replacedStmts))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => randInitModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
