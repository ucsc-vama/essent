package essent

import java.io.File

import scopt.OptionParser


case class OptFlags(
    java: Boolean = false,
    firInputFile: File = null,
    removeFlatConnects: Boolean = true,
    regUpdates: Boolean = true,
    conditionalMuxes: Boolean = true,
    useCondParts: Boolean = true,
    writeHarness: Boolean = false,
    dumpLoFirrtl: Boolean = false,
    trackSigs: Boolean = false,
    trackParts: Boolean = false,
    trackExts: Boolean = false,
    partStats: Boolean = false,
    partCutoff: Int = 8,
    essentLogLevel: String = "warn",
    firrtlLogLevel: String = "warn") {
  def inputFileDir() = firInputFile.getParent
  def outputDir() = if (inputFileDir == null) "" else inputFileDir()
}

class ArgsParser {
  val parser = new OptionParser[OptFlags]("essent") {
    arg[File]("<file>").required().unbounded().action( (x, c) =>
      c.copy(firInputFile = x) ).text(".fir input file")

    opt[Unit]("java").abbr("java").action( (_, c) => c.copy(
        java = true)
    ).text("java test")

    opt[Unit]("O0").abbr("O0").action( (_, c) => c.copy(
        removeFlatConnects = false,
        regUpdates = false,
        conditionalMuxes = false,
        useCondParts=false)
    ).text("disable all optimizations")

    opt[Unit]("O1").abbr("O1").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = false,
        useCondParts=false)
    ).text("enable only optimizations without conditionals")

    opt[Unit]("O2").abbr("O2").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = true,
        useCondParts=false)
    ).text("enable conditional evaluation of mux inputs")

    opt[Unit]("O3").abbr("O3").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = true,
        useCondParts=true)
    ).text("enable all optimizations (default)")

    opt[Unit]("dump").action( (_, c) => c.copy(
        dumpLoFirrtl = true)
    ).text("dump low-firrtl prior to essent executing")

    opt[Unit]('h', "harness").action( (_, c) => c.copy(
        writeHarness = true)
    ).text("generate harness for Verilator debug API")

    opt[String]("essent-log-level").abbr("ell").valueName("<Error|Warn|Info|Debug|Trace>")
    .validate { x =>
      if (Array("error", "warn", "info", "debug", "trace").contains(x.toLowerCase)) success
      else failure(s"$x bad value must be one of error|warn|info|debug|trace")
    }
    .action( (level, c) => c.copy(essentLogLevel = level ) )
    .text("logging level for essent processing after firrtl")

    opt[String]("firrtl-log-level").abbr("fll").valueName("<Error|Warn|Info|Debug|Trace>")
    .validate { x =>
      if (Array("error", "warn", "info", "debug", "trace").contains(x.toLowerCase)) success
      else failure(s"$x bad value must be one of error|warn|info|debug|trace")
    }
    .action( (level, c) => c.copy(firrtlLogLevel = level ) )
    .text("logging level for firrtl preprocessing")

    help("help").text("prints this usage text")

    opt[Unit]("activity-signal").action( (_, c) => c.copy(
        trackSigs = true)
    ).text("track individual signal activities")

    opt[Unit]("activity-parts").action( (_, c) => c.copy(
        useCondParts = true,
        trackParts = true)
    ).text("print out partition activity stats")

    opt[Unit]("activity-exts").action( (_, c) => c.copy(
        trackSigs = true,
        trackExts = true)
    ).text("track individual signal extinguishes (with activities)")

    opt[Unit]("stats-parts").action( (_, c) => c.copy(
        useCondParts = true,
        partStats = true)
    ).text("output topo information from partitioning")

    opt[Int]("part-cutoff").action( (x, c) => c.copy(
        partCutoff = x)
    ).text("parameter used for partitioning")
  }

  def getConfig(args: Seq[String]): Option[OptFlags] = parser.parse(args, OptFlags())
}

object TestFlags {
  def apply(inputFirFile: File): OptFlags = {
    OptFlags(firInputFile = inputFirFile, writeHarness = true)
  }
}
