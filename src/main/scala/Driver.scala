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
    val compiler = new CCCompiler(opt, dutWriter, debugWriter)
    compiler.compileAndEmit(CircuitState(circuit, firrtl.ChirrtlForm))
    dutWriter.close()
    debugWriter map { _.close() }
  }

  def setLoggingLevels(opt: OptFlags) {
    def parseLevel(levelStr: String) = levelStr.toLowerCase match {
      case "error" => LogLevel.Error
      case "warn"  => LogLevel.Warn
      case "info"  => LogLevel.Info
      case "debug" => LogLevel.Debug
      case "trace" => LogLevel.Trace
    }
    val baseClassNames = Seq("Emitter", "Extract$", "Graph", "StatementGraph")
    val baseLogLevel = parseLevel(opt.essentLogLevel)
    val baseClassLogLevels = (baseClassNames map {
      className => s"essent.$className" -> baseLogLevel}
    ).toMap
    Logger.setClassLogLevels(baseClassLogLevels)
    Logger.setClassLogLevels(Map("essent.passes" -> parseLevel(opt.passLogLevel)))
  }

  def compileCPP(dutName: String, buildDir: String): ProcessBuilder = {
    Seq("c++", "-O3", "-std=c++11", s"-I$buildDir", s"-Ifirrtl-sig",
      s"$buildDir/$dutName-harness.cc", "-o", s"$buildDir/$dutName")
  }
}
