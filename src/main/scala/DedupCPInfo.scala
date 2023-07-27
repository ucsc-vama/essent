package essent

import essent.Emitter.{emitExpr, genCppType}
import essent.Graph.NodeID
import essent.ir.{CondPart, MemWrite, RegUpdate}
import essent.Util.removeDots
import firrtl.ir.{DefMemory, Type}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class DedupCPInfo(sg: StatementGraph, dedupInstanceNames: Seq[String], mergeIdToCPid: mutable.HashMap[Int, Int], dedupMergeIdMap: mutable.HashMap[Int, mutable.ArrayBuffer[NodeID]]) {

  val dedupMainInstanceName = dedupInstanceNames.head
  val dedupInstanceNameList = dedupInstanceNames
  val dedupInstanceNameToId = dedupInstanceNames.zipWithIndex.toMap
  val mergeIDToCPID = mergeIdToCPid

  // CP id in main instance -> CP ids in other instances
  val dedupCPIdMap = dedupMergeIdMap.map{case (mainId, dupIds) => {
    val mainInstCPid = mergeIdToCPid(mainId)
    val dedupInstCPids = dupIds.map(mergeIdToCPid)
    mainInstCPid -> dedupInstCPids
  }}

  val dedupOtherCPToMainCPMap = dedupCPIdMap.flatMap{ case (mainId, otherIds) => {
    otherIds.map{oid => oid -> mainId}
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

  val cpidToMergeId = mergeIdToCPid.map{case (mergeid, cpid) => cpid -> mergeid}.toMap

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

        cp.memberStmts.collect{case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef)}.toSet.foreach {name: String => {
          // Write only
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


  def signalReadOnlyByDedup(name: String) = {
    inputSignalNameToCPid.getOrElse(name, Set[Int]()).forall(allDedupCPids.contains)
  }

  def signalWriteOnlyByDedup(name: String) = {
    outputSignalNameToCPid(name).forall(allDedupCPids.contains)
  }

  def signalWriteOnlyByOutside(name: String) = {
    if (outputSignalNameToCPid.contains(name)) {
      assert(outputSignalNameToCPid(name).size == 1)
      !signalWriteOnlyByDedup(name)
    } else true
  }


  val dedupInputSignals = allDedupCPids.flatMap{cpid => {
    val mergeId = cpidToMergeId(cpid)
    sg.idToStmt(mergeId) match {
      case cp: CondPart => cp.inputs
      case _ => throw new Exception("Should be a CondPart")
    }
  }}
  val dedupOutputSignals = allDedupCPids.flatMap{cpid => {
    val mergeId = cpidToMergeId(cpid)
    sg.idToStmt(mergeId) match {
      case cp: CondPart => cp.outputsToDeclare.keys
      case _ => throw new Exception("Should be a CondPart")
    }
  }}

  val mainInstInputSignals = dedupCPIdMap.keys.toSet.flatMap{cpid: NodeID => {
    val mergeId = cpidToMergeId(cpid)
    sg.idToStmt(mergeId) match {
      case cp: CondPart => cp.inputs
      case _ => throw new Exception("Should be a CondPart")
    }
  }}
  val mainInstOutputSignals = dedupCPIdMap.keys.toSet.flatMap{cpid: NodeID => {
    val mergeId = cpidToMergeId(cpid)
    sg.idToStmt(mergeId) match {
      case cp: CondPart => cp.outputsToDeclare.keys
      case _ => throw new Exception("Should be a CondPart")
    }
  }}

  val dedupRWSignalsByInst = dedupInstNameToCPids.map{case (name, cpids) => {
    val mergeIds = cpids.map(cpidToMergeId)
    val allRWSignals = mergeIds.flatMap{mid => sg.idToStmt(mid) match {
      case cp: CondPart => cp.inputs ++ cp.outputsToDeclare.keys
      case _ => throw new Exception("Should be a CondPart")
    }}.toSet
    name -> allRWSignals
  }}


  val replicatedSignalsToDeclareName = mainInstOutputSignals.map{canonicalName => {
    canonicalName -> removeDots(canonicalName.stripPrefix(dedupMainInstanceName))
  }}.toMap

//  // Note: A signal could have only 1 writer but may have multiple readers
//  // Thus dedupInternalSignals != (dedupOutputSignals & dedupInputSignals)
//  val dedupInternalSignals = dedupOutputSignals.filter(signalReadOnlyByDedup)
  val dedupMainInstWriteSignals = mainInstOutputSignals




  val allDedupInstRWSignals = (dedupInputSignals ++ dedupOutputSignals).toSet
  val allDedupInstInternalSignals = dedupOutputSignals.filter(signalReadOnlyByDedup)
  val allDedupInstBoundarySignals = allDedupInstRWSignals.diff(allDedupInstInternalSignals)

  val mainDedupInstRWSignals = mainInstInputSignals ++ mainInstOutputSignals
  val mainDedupInstInternalSignals = mainInstOutputSignals.filter(signalReadOnlyByDedup)
  val mainDedupInstBoundarySignals = mainDedupInstRWSignals.diff(mainDedupInstInternalSignals)
  // There should be no signal shared by different dedup instances, ensured by partitioner
  assert(allDedupInstBoundarySignals.size == mainDedupInstBoundarySignals.size * dedupInstanceNames.size)


  // Filled by MakeCondPart
  val signalNameToType = mutable.HashMap[String, Type]()

  // names for all registers and memory
  val allStmts = mergeIdToCPid.keys.toSeq.map(sg.idToStmt).flatMap{
    case cp: CondPart => cp.memberStmts
  }
  val allRegisterNames = allStmts.collect{case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef)}.toSet
  val allRegesterNameToTypeStr = allStmts.collect{case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef) -> genCppType(ru.regRef.tpe)}.toMap

  val dedupStmts = allDedupCPids.map(cpidToMergeId).map(sg.idToStmt).flatMap{case cp: CondPart => cp.memberStmts}
  val dedupWriteRegisterNames = dedupStmts.collect{case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef)}.toSet
  val dedupRegisterNames = allDedupInstRWSignals.intersect(allRegisterNames) ++ dedupWriteRegisterNames
//  val dedupMemoryNames = dedupStmts.collect{case m: DefMemory => m}.map{m => m.name}

  val dedupStmtsByInst = dedupInstNameToCPids.map{case (instName, cpIds) => {
    instName -> cpIds.map(cpidToMergeId).map(sg.idToStmt).flatMap{case cp: CondPart => cp.memberStmts}
  }}
  val dedupRegisterNamesByInst = dedupRWSignalsByInst.map{case (instName, signals) => {
    val instStmts = dedupInstNameToCPids(instName).map(cpidToMergeId).map(sg.idToStmt).flatMap{case cp: CondPart => cp.memberStmts}
    val instWriteRegisterNames = instStmts.collect{case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef)}.toSet
    instName -> (signals.intersect(allRegisterNames) ++ instWriteRegisterNames)
  }}
  assert(dedupRegisterNamesByInst.values.flatten.toSet.size == dedupRegisterNames.toSet.size)

  val dedupMainStmts = dedupCPIdMap.keys.toSeq.map(cpidToMergeId).map(sg.idToStmt).flatMap{case cp: CondPart => cp.memberStmts}
  val dedupMainRegisterNames = dedupRegisterNamesByInst(dedupMainInstanceName)
//  val dedupMainMemoryNames = dedupMainStmts.collect{case m: DefMemory => m}.map{m => m.name}

  // val allMemoryNameAndType = mutable.HashMap[String, Type]()
  val allMemoryNames = allStmts.collect{case mw: MemWrite => mw.memName}.toSet

  // Read mems (and possibly write mems) ++ Write mems
  val dedupMWNames = dedupStmts.collect{case mw: MemWrite => mw.memName}
  val dedupAccessedMemory = allMemoryNames.filter(allDedupInstRWSignals) ++ dedupMWNames
  val dedupAccessedMemoryByInst = dedupRWSignalsByInst.map{case(instName, signals) => {
    val instMemWriteNames = dedupStmtsByInst(instName).collect{case mw: MemWrite => mw.memName}
    instName -> (signals.intersect(dedupAccessedMemory) ++ instMemWriteNames)
  }}
  val outsideAccessedMemory = allMemoryNames.filterNot(dedupAccessedMemory)

}
