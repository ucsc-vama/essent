package saga

import collection.mutable.HashMap
import java.io.Writer

import firrtl._
import firrtl.Annotations._
import firrtl.ir._
import firrtl.Mappers._

object DevHelpers {
  // assumption: registers can only appear in blocks since whens expanded
  def findRegisters(s: Statement): Seq[DefRegister] = s match {
    case b: Block => b.stmts flatMap findRegisters
    case d: DefRegister => Seq(d)
    case _ => Seq()
  }

  val nodeMap = collection.mutable.HashMap[String, Expression]()

  def lastConnected(s: Statement): Statement = {
    s match {
      case Connect(_, loc, expr) => loc match {
        case w: WRef => nodeMap(w.name) = expr
        case _ =>
      }
      case DefNode(_, name, value) => nodeMap(name) = value
      case _ =>
    }
    s map lastConnected
    s
  }

  def traceRefs(name: String): Expression = nodeMap(name) match {
    case w: WRef => traceRefs(w.name)
    case s => s
  }

  def identifyWE(e: Expression) = e match {
    case m: Mux => m.cond match {
      case w: WRef => w.name
      case s =>
    }
    case e =>
  }

  def generateHarness(circuitName: String, writer: Writer) = {
    val baseStr = s"""|#include <iostream>
                      |
                      |#include "comm_wrapper.h"
                      |#include "$circuitName.h"
                      |
                      |int main() {
                      |  $circuitName dut;
                      |  CommWrapper<$circuitName> comm(dut);
                      |  comm.init_channels();
                      |  while (!comm.done()) {
                      |    comm.tick();
                      |  }
                      |  return 0;
                      |}
                      """.stripMargin
    writer write baseStr
  }
}


class DevTransform extends Transform {
  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    circuit.modules.head match {
      case m: Module => {
        val registers = DevHelpers.findRegisters(m.body)
        val regNames = registers map (_.name)
        DevHelpers.lastConnected(m.body)
        val lastExp = regNames map DevHelpers.traceRefs
        val writeEnables = lastExp map DevHelpers.identifyWE
        println(regNames zip writeEnables)
      }
      case m: ExtModule =>
    }
    TransformResult(circuit)
  }
}


class EmitCpp(writer: Writer) extends Transform {
  val tabs = "  "

  def genCppType(tpe: Type) = tpe match {
    case UIntType(w) => "unsigned int"
    case SIntType(w) => "int"
    case _ =>
  }

  def processPort(p: Port): Seq[String] = p.tpe match {
    case ClockType => Seq()
    case _ => Seq(genCppType(p.tpe) + " " + p.name + ";")
  }

  def processExpr(e: Expression): String = e match {
    case w: WRef => w.name
    case u: UIntLiteral => "0x" + u.value.toString(16)
    case m: Mux => {
      val condName = processExpr(m.cond)
      val tvalName = processExpr(m.tval)
      val fvalName = processExpr(m.fval)
      s"$condName ? $tvalName : $fvalName"
    }
    case _ => ""
  }

  def processStmt(s: Statement): Seq[String] = s match {
    case b: Block => b.stmts flatMap processStmt
    case d: DefNode => {
      val lhs = genCppType(d.value.tpe) + " " + d.name
      val rhs = processExpr(d.value)
      Seq(s"$lhs = $rhs;")
    }
    case c: Connect => {
      val lhs = processExpr(c.loc)
      val rhs = processExpr(c.expr)
      Seq(s"$lhs = $rhs;")
    }
    case _ => Seq()
  }

  def makeResetIf(r: DefRegister): String = {
    val regName = r.name
    val resetName = processExpr(r.reset)
    val resetVal = processExpr(r.init)
    s"if ($resetName) $regName = $resetVal;"
  }

  def processModule(m: Module) = {
    val registers = DevHelpers.findRegisters(m.body)
    val variableDecs = registers map {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regName = d.name
      s"$typeStr $regName;"
    }}

    val modName = m.name
    val headerGuardName = modName.toUpperCase + "_H_"

    writer write s"#ifndef $headerGuardName\n"
    writer write s"#define $headerGuardName\n\n"
    writer write "typedef struct {\n"
    variableDecs foreach { d => writer write (tabs + d + "\n") }
    m.ports flatMap processPort foreach { d => writer write (tabs + d + "\n") }
    writer write "\n" + tabs + "void eval() {\n"  
    processStmt(m.body) foreach { d => writer write (tabs*2 + d + "\n") }
    registers map makeResetIf foreach { d => writer write (tabs*2 + d + "\n") }
    writer write tabs + "}\n"
    writer write s"}  $modName;\n\n"
    writer write s"#endif  // $headerGuardName\n"
  }

  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    circuit.modules foreach {
      case m: Module => processModule(m)
      case m: ExtModule =>
    }
    println(circuit.serialize)
    TransformResult(circuit)
  }
}

class CCCompiler extends Compiler {
  def transforms(writer: Writer): Seq[Transform] = Seq(
    new firrtl.Chisel3ToHighFirrtl,
    new firrtl.IRToWorkingIR,
    new firrtl.ResolveAndCheck,
    new firrtl.HighFirrtlToMiddleFirrtl,
    new firrtl.passes.InferReadWrite(TransID(-1)),
    new firrtl.passes.ReplSeqMem(TransID(-2)),
    new firrtl.MiddleFirrtlToLowFirrtl,
    new firrtl.passes.InlineInstances(TransID(0)),
    // new DevTransform,
    new EmitCpp(writer)
    // new firrtl.EmitFirrtl(writer)
  )
}
