package essent
import org.scalatest.flatspec.AnyFlatSpec
import essent.passes.ReplaceRsvdKeywords
import firrtl.CircuitState
import firrtl.options.Dependency

import java.io.{File, FileWriter}
import scala.io.Source

class ReplaceRsvdKeyTest extends AnyFlatSpec{
   "Mypass" should "Replace all reserve keyword" in {
     val sourceReader = Source.fromURL(getClass.getResource("/ReplacedRsvdKey.fir"))
     val circuit = firrtl.Parser.parse(sourceReader.getLines, firrtl.Parser.IgnoreInfo)
     sourceReader.close()
     val deps = firrtl.stage.Forms.LowFormOptimized ++ Seq(Dependency(ReplaceRsvdKeywords))
     val firrtlCompiler = new firrtl.stage.transforms.Compiler(deps)
     val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
     val CorrectReader = Source.fromURL(getClass.getResource("/ReplacedRsvdKey_correct.fir"))
     val correctString = CorrectReader.getLines.mkString("\n")
     assert(correctString == resultState.circuit.serialize)
    }
}


