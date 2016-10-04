package saga

import java.io.Writer

import firrtl._
import firrtl.Annotations._


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
    new firrtl.EmitFirrtl(writer)
  )
}
