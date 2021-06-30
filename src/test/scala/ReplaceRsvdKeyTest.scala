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
     sourceReader.close()

     val deps = firrtl.stage.Forms.LowFormOptimized ++ Seq(Dependency(ReplaceRsvdKeywords))
     val firrtlCompiler = new firrtl.stage.transforms.Compiler(deps)
     val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
     val tmpfile = File.createTempFile(s"${circuit.main}_transformed",".fir")
     println(tmpfile)
     val sourceReader1 = Source.fromURL(getClass.getResource("/ReplacedRsvdKey_correct.fir"))
     val sourceReader2 = Source.fromFile(tmpfile)
    // assert(sourceReader1.getLines().sameElements(sourceReader2.getLines()))
    // tmpfile.delete()
  }
}


