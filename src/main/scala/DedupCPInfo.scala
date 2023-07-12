package essent

import essent.Graph.NodeID
import essent.ir.CondPart

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class DedupCPInfo(sg: StatementGraph, dedupInstanceNames: Seq[String], mergeIdToCPid: mutable.HashMap[Int, Int], dedupMergeIdMap: mutable.HashMap[Int, mutable.ArrayBuffer[NodeID]]) {

  val dedupMainInstanceName = dedupInstanceNames.head

  // CP id in main instance -> CP ids in other instances
  val dedupCPIdMap = dedupMergeIdMap.map{case (mainId, dupIds) => {
    val mainInstCPid = mergeIdToCPid(mainId)
    val dedupInstCPids = dupIds.map(mergeIdToCPid)
    mainInstCPid -> dedupInstCPids
  }}

  // Instance name -> All CP ids
  val dedupInstNameToCPids = dedupInstanceNames.zipWithIndex.map{ case (instName, idx) => {
    val cpIds = new ArrayBuffer[NodeID]()
    if (instName == dedupMainInstanceName) {
      cpIds ++= dedupMergeIdMap.keys.map(mergeIdToCPid).toSet
    } else {
      val instMergeIds = dedupMergeIdMap.values.map(_(idx - 1))
      cpIds ++= instMergeIds.map(mergeIdToCPid).toSet
    }
    instName -> cpIds
  }}.toMap



  val inputSignalNameToCPid = mutable.HashMap[String, Set[NodeID]]()
  val outputSignalNameToCPid = mutable.HashMap[String, Set[NodeID]]()

  val allDedupCPids = (dedupCPIdMap.keys.toSeq ++ dedupCPIdMap.values.flatten).toSet

  mergeIdToCPid.foreach{case (mid, cpid) => {
    sg.idToStmt(mid) match {
      case cp: CondPart => {

        cp.outputsToDeclare.foreach{case (name, tpe) => {
          if (!outputSignalNameToCPid.contains(name)) {
            outputSignalNameToCPid(name) = Set[Int]()
          }
          outputSignalNameToCPid(name) += cpid
        }}

        cp.inputs.foreach{case name => {
          if (!inputSignalNameToCPid.contains(name)) {
            inputSignalNameToCPid(name) = Set[Int]()
          }
          inputSignalNameToCPid(name) += cpid
        }}
      }
      case _ => throw new Exception("Shouldnt reach here")
    }
  }}

  val cpIdToDedupInstName = new mutable.HashMap[Int, String]()
  dedupInstNameToCPids.foreach{case (instName, cpIds) => {
    cpIds.foreach{cpId => {
      cpIdToDedupInstName(cpId) = instName
    }}
  }}

}
