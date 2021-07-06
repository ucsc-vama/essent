package essent
import org.scalatest._
import essent.passes.ReplaceRsvdKeywords
import firrtl.CircuitState
import firrtl.options.Dependency

import java.io.{File, FileWriter}
import scala.io.Source

class ReplaceRsvdKeyTest extends FlatSpec{
   "Mypass" should "Replace all reserve keyword" in {
     val sourceReader = Source.fromURL(getClass.getResource("/ReplacedRsvdKey.fir"))
     val circuit = firrtl.Parser.parse(sourceReader.getLines, firrtl.Parser.IgnoreInfo)
     val deps = firrtl.stage.Forms.LowFormOptimized ++ Seq(Dependency(ReplaceRsvdKeywords))
     val firrtlCompiler = new firrtl.stage.transforms.Compiler(deps)
     val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
     val sourceReader1 = Source.fromURL(getClass.getResource("/ReplacedRsvdKey_correct.fir"))
     val lines1 = sourceReader1.getLines()
     val lines2 = sourceReader.getLines()
     val cnt = (lines1 zip lines2).count { case (a, b) => a != b }
     assert(cnt===0)
     }
}


