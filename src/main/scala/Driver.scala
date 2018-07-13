package essent

import java.io.{File, FileWriter}
import scala.io.Source
import scala.sys.process._

import firrtl._
import firrtl.ir._


object Driver {
  def main(args: Array[String]) = {
    (new ArgsParser).getConfig(args) match {
      case Some(config) => generate(config)
      case None =>
    }
  }

  def generate(opt: OptFlags) {
    val inputFileDir = opt.firInputFile.getParent()
    val outputDir = if (inputFileDir == null) "" else inputFileDir
    val circuit = firrtl.Parser.parse(Source.fromFile(opt.firInputFile).getLines,
                                      firrtl.Parser.IgnoreInfo)
    val topName = circuit.main
  
    if (opt.writeHarness) {
      val harnessFilename = new File(outputDir, s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      HarnessGenerator.topFile(topName, harnessWriter)
      harnessWriter.close()
    }

    val dutWriter = new FileWriter(new File(outputDir, s"$topName.h"))
    val debugWriter = if (opt.dumpLoFirrtl) Some(new FileWriter(new File(outputDir, s"$topName.lo.fir")))
                      else None
    val compiler = new CCCompiler(opt, dutWriter, debugWriter)
    compiler.compileAndEmit(CircuitState(circuit, firrtl.ChirrtlForm))
    dutWriter.close()
    debugWriter map { _.close() }
  }

  def compileCPP(dutName: String, buildDir: String): ProcessBuilder = {
    Seq("g++", "-O3", "-std=c++11", "-Icsrc/", s"-I$buildDir", s"-I../big-sig",
      s"$buildDir/$dutName-harness.cc", "-o", s"$buildDir/$dutName")
  }
}
