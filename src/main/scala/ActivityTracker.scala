package essent

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import firrtl.ir._

import java.io.Writer

class ActivityTracker(w: Writer, opt: OptFlags) {
  val actVarName = "ACTcounts"
  val sigTrackName = "SIGcounts"
  val sigActName = "SIGact"
  val sigExtName = "SIGext"
  var sigNameToID = Map[String, Int]()

  def declareTop(sg: StatementGraph, topName: String, condPartWorker: MakeCondPart): Unit = {
    w.writeLines(0, "#include \"../SimpleJSON/json.hpp\"")
    w.writeLines(0, "using json::JSON;")
    w.writeLines(0, "uint64_t act_cycle_count = 0;")
     if (opt.trackSigs)
       declareSigTracking(sg, topName)
     if (opt.trackParts)
       w.writeLines(1, s"std::array<uint64_t,${condPartWorker.getNumParts()}> $actVarName{};")
     if (opt.trackParts || opt.trackSigs)
        emitJsonWriter(condPartWorker.getNumParts())
    // if (opt.trackExts)
    //   sg.dumpNodeTypeToJson(sigNameToID)
    // sg.reachableAfter(sigNameToID)
  }

  def declareSigTracking(sg: StatementGraph, topName: String): Unit = {
    val allNamesAndTypes = sg.collectValidStmts(sg.nodeRange) flatMap findStmtNameAndType
    sigNameToID = (allNamesAndTypes map {
      _._1
    }).zipWithIndex.toMap
    w.writeLines(0, "")
    w.writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigTrackName{};")
    if (opt.trackExts) {
      w.writeLines(0, s"std::array<bool,${sigNameToID.size}> $sigActName{};")
      w.writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigExtName{};")
    }
    w.writeLines(0, "namespace old {")
    w.writeLines(1, allNamesAndTypes map {
      case (name, tpe) => s"${genCppType(tpe)} ${name.replace('.', '$')};"
    })
    w.writeLines(0, "}")
  }

  def emitSigTracker(stmt: Statement, indentLevel: Int): Unit = {
    stmt match {
      case mw: MemWrite =>
      case _ => {
        val resultName = findResultName(stmt)
        resultName match {
          case Some(name) => {
            val cleanName = name.replace('.', '$')
            w.writeLines(indentLevel, s"$sigTrackName[${sigNameToID(name)}] += $name != old::$cleanName ? 1 : 0;")
            if (opt.trackExts) {
              w.writeLines(indentLevel, s"$sigActName[${sigNameToID(name)}] = $name != old::$cleanName;")
              val depNames = findDependencesStmt(stmt).head.deps
              val trackedDepNames = depNames filter sigNameToID.contains
              val depTrackers = trackedDepNames map { name => s"$sigActName[${sigNameToID(name)}]" }
              val anyDepActive = depTrackers.mkString(" || ")
              if (anyDepActive.nonEmpty)
                w.writeLines(indentLevel, s"$sigExtName[${sigNameToID(name)}] += !$sigActName[${sigNameToID(name)}] && ($anyDepActive) ? 1 : 0;")
            }
            w.writeLines(indentLevel, s"old::$cleanName = $name;")
          }
          case None =>
        }
      }
    }
  }

  def emitJsonWriter(numParts: Int): Unit = {
    w.writeLines(0, "void writeActToJson() {")
    w.writeLines(1, "std::fstream file(\"activities.json\", std::ios::out | std::ios::binary);")
    w.writeLines(1, "JSON all_data;")
    if (opt.trackSigs) {
      w.writeLines(1, "JSON sig_acts;")
      w.writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      w.writeLines(2, s"""sig_acts[i] = JSON({"id", i, "acts", $sigTrackName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"signal-activities\"] = sig_acts;")
    }
    if (opt.trackParts) {
      w.writeLines(1, "JSON part_acts;")
      w.writeLines(1, s"for (int i=0; i<$numParts; i++) {")
      w.writeLines(2, s"""part_acts[i] = JSON({"id", i, "acts", $actVarName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"part-activities\"] = part_acts;")
    }
    if (opt.trackExts) {
      w.writeLines(1, "JSON sig_exts;")
      w.writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      w.writeLines(2, s"""sig_exts[i] = JSON({"id", i, "exts", $sigExtName[i]});""")
      w.writeLines(1, "}")
      w.writeLines(1, "all_data[\"sig-extinguishes\"] = sig_exts;")
    }
    w.writeLines(1, "all_data[\"cycles\"] = act_cycle_count;")
    w.writeLines(1, "file << all_data << std::endl;")
    w.writeLines(1, "file.close();")
    w.writeLines(0, "}")
  }
}
