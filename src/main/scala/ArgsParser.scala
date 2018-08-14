package essent

import java.io.File

import scopt.OptionParser


case class OptFlags(
    firInputFile: File = null,
    regUpdates: Boolean = true,
    muxShadows: Boolean = true,
    zoneAct: Boolean = true,
    writeHarness: Boolean = false,
    dumpLoFirrtl: Boolean = false,
    trackAct: Boolean = false,
    passLogLevel: String = "warn",
    essentLogLevel: String = "warn")

class ArgsParser {
  val parser = new OptionParser[OptFlags]("essent") {
    opt[Unit]("O0").abbr("O0").action( (_, c) => c.copy(
        regUpdates = false,
        muxShadows = false,
        zoneAct=false)
    ).text("disable all optimizations")

    opt[Unit]("O1").abbr("O1").action( (_, c) => c.copy(
        regUpdates = true,
        muxShadows = false,
        zoneAct=false)
    ).text("enable only optimizations without conditionals")

    opt[Unit]("O2").abbr("O2").action( (_, c) => c.copy(
        regUpdates = true,
        muxShadows = true,
        zoneAct=false)
    ).text("enable conditional evaluation of mux inputs")

    opt[Unit]("O3").abbr("O3").action( (_, c) => c.copy(
        regUpdates = true,
        muxShadows = true,
        zoneAct=true)
    ).text("enable all optimizations (default)")

    opt[Unit]("dump").action( (_, c) => c.copy(
        dumpLoFirrtl = true)
    ).text("dump low-firrtl prior to essent executing")

    opt[Unit]('h', "harness").action( (_, c) => c.copy(
        writeHarness = true)
    ).text("generate harness for Verilator debug API")

    opt[Unit]("activity-stats").action( (_, c) => c.copy(
        zoneAct = true,
        trackAct = true)
    ).text("print out zone activity stats")

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

    arg[File]("<file>").required().unbounded().action( (x, c) =>
      c.copy(firInputFile = x) ).text(".fir input file")
  }

  def getConfig(args: Seq[String]): Option[OptFlags] = parser.parse(args, OptFlags())
}

object TestFlags {
  def apply(inputFirFile: File): OptFlags = {
    OptFlags(
      firInputFile = inputFirFile,
      regUpdates = true,
      muxShadows = true,
      zoneAct = false,
      writeHarness = true,
      dumpLoFirrtl = false,
      trackAct = false,
      passLogLevel = "warn",
      essentLogLevel = "warn"
    )
  }
}
