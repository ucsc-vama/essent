package saga

import java.io.Writer

import firrtl._
import firrtl.Annotations._
import firrtl.ir._
import firrtl.Mappers._


object DevHelpers {
  def findRegisters(s: Statement): Seq[(String,Type)] = {
    s match {
      case b: Block => b.stmts flatMap findRegisters
      case DefRegister(_, name, tpe, _, _, _) => Seq((name,tpe))
      case _ => Seq()
    }
  }
}

class DevTransform extends Transform {
  def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = {
    val r = circuit.modules.head match {
      case m: Module => DevHelpers.findRegisters(m.body)
      case m: ExtModule =>
    }
    println(r)
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
    new DevTransform,
    new firrtl.EmitFirrtl(writer)
  )
}
