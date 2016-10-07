package saga

import java.io.{File, FileWriter}
import scala.io.Source

import firrtl._

object Driver {
  def main(args: Array[String]) = {
    val argsList = args.toList
    if (argsList.isEmpty)
      throw new Exception("Please give input .fir file")
    val inputFirFile = argsList.head
    val outputPathResp = new File(inputFirFile).getParent()
    val outputPath = if (outputPathResp == null) "" else outputPathResp
    val parsedInput = firrtl.Parser.parse(Source.fromFile(inputFirFile).getLines,
                                          firrtl.Parser.IgnoreInfo)
    val topName = parsedInput.main
  
    val harnessFilename = new File(outputPath, s"$topName-harness.cc")
    val harnessWriter = new FileWriter(harnessFilename)
    DevHelpers.generateHarness(topName, harnessWriter)
    harnessWriter.close()

    val dutWriter = new FileWriter(new File(outputPath, s"$topName.h"))
    val annotations = new firrtl.Annotations.AnnotationMap(Seq.empty)
    val compiler = new CCCompiler
    compiler.compile(parsedInput, annotations, dutWriter)
    dutWriter.close()
  }
}
