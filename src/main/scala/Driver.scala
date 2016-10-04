package saga

import scala.io.Source

import firrtl._

object Driver {
  def main(args: Array[String]) = {
    val argsList = args.toList
    if (argsList.isEmpty)
      throw new Exception("Please give input .fir file")
    val inputFirFile = argsList.head
    val parsedInput = firrtl.Parser.parse(Source.fromFile(inputFirFile).getLines,
                                          firrtl.Parser.IgnoreInfo)
    
    val annotations = new firrtl.Annotations.AnnotationMap(Seq.empty)
    val outputBuffer = new java.io.CharArrayWriter
    val highComp = new firrtl.HighFirrtlCompiler
    highComp.compile(parsedInput, annotations, outputBuffer)
    print(outputBuffer)
  }
}
