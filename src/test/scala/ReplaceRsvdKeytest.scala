import essent.passes.ReplaceRsvdKeywords
import firrtl.CircuitState
import firrtl.options.Dependency

import java.io.{File, FileWriter}
import scala.io.Source

object ReplaceRsvdKeytest extends App {
  val sourceReader = Source.fromFile(args(0))
  val circuit = firrtl.Parser.parse(sourceReader.getLines, firrtl.Parser.IgnoreInfo)
  sourceReader.close()

  val deps = firrtl.stage.Forms.LowFormOptimized ++ Seq(Dependency(ReplaceRsvdKeywords))
  val firrtlCompiler = new firrtl.stage.transforms.Compiler(deps)
  val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
  val debugWriter = new FileWriter(new File(s"${circuit.main}_transformed.fir"))
  debugWriter.write(resultState.circuit.serialize)
  debugWriter.close()
}

