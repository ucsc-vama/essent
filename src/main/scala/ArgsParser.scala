package essent

import java.io.File

import scopt.OptionParser


case class OptFlags(
    firInputFile: File = null,
    removeFlatConnects: Boolean = true,
    regUpdates: Boolean = true,
    conditionalMuxes: Boolean = true,
    useZones: Boolean = true,
    writeHarness: Boolean = false,
    dumpLoFirrtl: Boolean = false,
    trackSigs: Boolean = false,
    trackZone: Boolean = false,
    trackExts: Boolean = false,
    zoneStats: Boolean = false,
    zoneCutoff: Int = 20,
    passLogLevel: String = "warn",
    essentLogLevel: String = "warn")

class ArgsParser {
  val parser = new OptionParser[OptFlags]("essent") {
    arg[File]("<file>").required().unbounded().action( (x, c) =>
      c.copy(firInputFile = x) ).text(".fir input file")

    opt[Unit]("O0").abbr("O0").action( (_, c) => c.copy(
        removeFlatConnects = false,
        regUpdates = false,
        conditionalMuxes = false,
        useZones=false)
    ).text("disable all optimizations")

    opt[Unit]("O1").abbr("O1").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = false,
        useZones=false)
    ).text("enable only optimizations without conditionals")

    opt[Unit]("O2").abbr("O2").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = true,
        useZones=false)
    ).text("enable conditional evaluation of mux inputs")

    opt[Unit]("O3").abbr("O3").action( (_, c) => c.copy(
        removeFlatConnects = true,
        regUpdates = true,
        conditionalMuxes = true,
        useZones=true)
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
    .text("Logging level for essent not during passes")

    opt[String]("pass-log-level").abbr("pll").valueName("<Error|Warn|Info|Debug|Trace>")
    .validate { x =>
      if (Array("error", "warn", "info", "debug", "trace").contains(x.toLowerCase)) success
      else failure(s"$x bad value must be one of error|warn|info|debug|trace")
    }
    .action( (level, c) => c.copy(passLogLevel = level ) )
    .text("Logging level for essent during passes")

    help("help").text("prints this usage text")

    opt[Unit]("activity-signal").action( (_, c) => c.copy(
        trackSigs = true)
    ).text("track individual signal activities")

    opt[Unit]("activity-zone").action( (_, c) => c.copy(
        useZones = true,
        trackZone = true)
    ).text("print out zone activity stats")

    opt[Unit]("activity-exts").action( (_, c) => c.copy(
        trackSigs = true,
        trackExts = true)
    ).text("track individual signal extinguishes (with activities)")

    opt[Unit]("stats-zone").action( (_, c) => c.copy(
        useZones = true,
        zoneStats = true)
    ).text("output topo information from zoning partitioning")

    opt[Int]("zone-cutoff").action( (x, c) => c.copy(
        zoneCutoff = x)
    ).text("parameter used for zoning")
  }

  def getConfig(args: Seq[String]): Option[OptFlags] = parser.parse(args, OptFlags())
}

object TestFlags {
  def apply(inputFirFile: File): OptFlags = {
    OptFlags(firInputFile = inputFirFile, writeHarness = true)
  }
}
