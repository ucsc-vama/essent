package essent

import java.io.{File, FileWriter}

import scala.io.Source
import scala.sys.process._
import firrtl._
import firrtl.ir._
import logger._


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
    setLoggingLevels(opt)

    if (opt.writeHarness) {
      val harnessFilename = new File(outputDir, s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      HarnessGenerator.topFile(topName, harnessWriter)
      harnessWriter.close()
    }

    val dutWriter = new FileWriter(new File(outputDir, s"$topName.h"))
    val debugWriter = if (opt.dumpLoFirrtl) Some(new FileWriter(new File(outputDir, s"$topName.lo.fir")))
                      else None
    val compiler = new EssentCompiler(opt, dutWriter)
    compiler.compileAndEmit(circuit)
    dutWriter.close()
    debugWriter map { _.close() }
  }

  def setLoggingLevels(opt: OptFlags) {
    Logger.setClassLogLevels(Map("essent" -> logger.LogLevel(opt.essentLogLevel)))
    Logger.setClassLogLevels(Map("firrtl" -> logger.LogLevel(opt.firrtlLogLevel)))
  }

  def compileCPP(dutName: String, buildDir: String): ProcessBuilder = {
    Seq("g++", "-O3", "-std=c++11", s"-I$buildDir", s"-Ifirrtl-sig",
      s"$buildDir/$dutName-harness.cc", "-o", s"$buildDir/$dutName")
  }
}
