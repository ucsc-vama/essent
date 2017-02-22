package essent

import java.io.{File, FileWriter}
import scala.io.Source
import scala.sys.process._

import firrtl._
import firrtl.ir._


object Driver {
  def main(args: Array[String]) = {
    val argsList = args.toList
    if (argsList.isEmpty)
      throw new Exception("Please give input .fir file")
    val verbose = argsList.head == "-v"
    val inputFirFile = argsList.last
    val inputFileDir = new File(inputFirFile).getParent()
    val outputDir = if (inputFileDir == null) "" else inputFileDir
    val parsedInput = firrtl.Parser.parse(Source.fromFile(inputFirFile).getLines,
                                          firrtl.Parser.IgnoreInfo)
    generate(parsedInput, outputDir, verbose)
  }

  def generate(circuit: Circuit, outputDir: String, verbose: Boolean = true) {
    val topName = circuit.main
  
    val harnessFilename = new File(outputDir, s"$topName-harness.cc")
    val harnessWriter = new FileWriter(harnessFilename)
    HarnessGenerator.topFile(topName, harnessWriter)
    harnessWriter.close()

    val dutWriter = new FileWriter(new File(outputDir, s"$topName.h"))
    val annotations = new firrtl.Annotations.AnnotationMap(Seq.empty)
    val compiler = new CCCompiler(verbose)
    compiler.compile(circuit, annotations, dutWriter)
    dutWriter.close()
  }

  def compileCPP(dutName: String, buildDir: String): ProcessBuilder = {
    Seq("g++", "-O3", "-std=c++11", "-Icsrc/", s"-I$buildDir", s"-I../big-sig",
      s"$buildDir/$dutName-harness.cc", "-o", s"$buildDir/$dutName",
      "-lgmpxx", "-lgmp")
    // Seq("g++", "-O3", "-std=c++11", "-Icsrc/", s"-I$buildDir",
    //   s"$buildDir/$dutName-harness.cc", "-o", s"$buildDir/$dutName",
    //   "-lgmpxx", "-lgmp")
  }
}
