package essent

import essent.Graph.NodeID
import essent.Extract._
import essent.ir._
import firrtl.ir._
import _root_.logger._
import essent.DedupWorker.alignInstance

import collection.mutable.ArrayBuffer
import scala.collection.mutable
import scala.reflect.ClassTag


class MakeCondPart(sg: StatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) extends LazyLogging {
  val cacheSuffix = "$old"

  val alreadyDeclared = sg.stateElemNames().toSet

  def convertIntoCPStmts(ap: AcyclicPart, excludedIDs: Set[NodeID]) {
    val idToMemberIDs = ap.iterParts
    val idToMemberStmts = (idToMemberIDs map { case (id, members) => {
      val memberStmts = sg.idToStmt(id) match {
        case cp: CondPart => cp.memberStmts
        case _ => members map sg.idToStmt
      }
      (id -> memberStmts)
    }}).toMap
    val idToProducedOutputs = idToMemberStmts mapValues { _ flatMap findResultName }
    val idToInputNames = idToMemberStmts map { case (id, memberStmts) => {
      val partDepNames = memberStmts flatMap findDependencesStmt flatMap { _.deps }
      val externalDepNames = partDepNames.toSet -- (idToProducedOutputs(id).toSet -- alreadyDeclared)
      (id -> externalDepNames.toSeq)
    }}
    val allInputs = idToInputNames.values.flatten.toSet
    val validParts = (idToMemberIDs flatMap { case (id, members) => {
      if (members.exists(sg.validNodes)) Seq(id)
      else Seq()
    }}).toSet
    val partsTopoSorted = TopologicalSort(ap.mg) filter validParts
    partsTopoSorted.zipWithIndex foreach { case (id, topoOrder) => {
      val consumedOutputs = idToProducedOutputs(id).toSet.intersect(allInputs)
      val namesToDeclare = consumedOutputs -- alreadyDeclared
      val nameToStmts = idToMemberStmts(id) map { stmt => (findResultName(stmt) -> stmt) }
      val outputsToDeclare = nameToStmts collect {
        case (Some(name), stmt) if namesToDeclare.contains(name) => (name -> findResultType(stmt))
      }
      val alwaysActive = excludedIDs.contains(id)
      val cpStmt = CondPart(topoOrder, alwaysActive, idToInputNames(id),
                                idToMemberStmts(id), outputsToDeclare.toMap)
      sg.mergeStmtsMutably(id, idToMemberIDs(id) diff Seq(id), cpStmt)
      namesToDeclare foreach { name => {
        rn.mutateDecTypeIfLocal(name, PartOut) }
        rn.addPartCache(name + cacheSuffix, rn.nameToMeta(name).sigType)
      }
      assert(sg.validNodes(id))
    }}
    val externalInputs = getExternalPartInputTypes(extIOtypes)
    externalInputs foreach {
      case (name, tpe) => rn.addPartCache(name + cacheSuffix, tpe)
    }
  }

  def clumpByStmtType[T <: Statement]()(implicit tag: ClassTag[T]): Option[Int] = {
    val matchingIDs = sg.idToStmt.zipWithIndex collect { case (t: T, id: Int) => id }
    if (matchingIDs.isEmpty) None
    else {
      val newGroupID = matchingIDs.min
      val memberStmts = matchingIDs map sg.idToStmt
      val tempCPstmt = CondPart(newGroupID, true, Seq(), memberStmts, Map())
      sg.mergeStmtsMutably(newGroupID, matchingIDs diff Seq(newGroupID), tempCPstmt)
      Some(newGroupID)
    }
  }

  def doOpt(smallPartCutoff: Int = 20) {
    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)
    val ap = AcyclicPart(sg, excludedIDs.toSet)
    ap.partition(smallPartCutoff)
    convertIntoCPStmts(ap, excludedIDs.toSet)
    logger.info(partitioningQualityStats())
  }

  def doOptForDedup(smallPartCutoff: Int, dedupInstances: Seq[String], modInstInfo: ModuleInstanceInfo) {

    val dedupMainInstanceName = dedupInstances.head
    val dedupMainInstanceNodes = modInstInfo.instInclusiveNodesTable(dedupMainInstanceName)
    val dedupRemainingInstances = dedupInstances.filter(_ != dedupMainInstanceName)

    val dedupMainInstancePartitions = mutable.HashMap[NodeID, Seq[NodeID]]()

    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)

    // 1. Only partition nodes for main dedup instqance
    val excludeIDsForDedup1 = excludedIDs.clone() ++ sg.nodeRange().filterNot(dedupMainInstanceNodes.contains)
    var ap = AcyclicPart(sg, excludeIDsForDedup1.toSet)
    ap.partition(smallPartCutoff)

    // Collect partition result
    ap.mg.mergeIDToMembers.foreach{case (mergeId, members) => {
      val groupInDedupInst = members.map(dedupMainInstanceNodes.contains).reduce(_&_)
      if (groupInDedupInst){
        dedupMainInstancePartitions(mergeId) = members
      }
    }}

    // Table that stores corresponding mergeIDs
    val dedupMergeIdMap = mutable.HashMap[Int, mutable.ArrayBuffer[NodeID]]()
    dedupMainInstancePartitions.foreach{case (mergeId, _) => {
      dedupMergeIdMap(mergeId) = new ArrayBuffer[NodeID]()
    }}


    // 2. Propagate partitioning from main instance to other dedup instances
    ap = AcyclicPart(ap.mg, excludedIDs.toSet)
    // Align remaining dedup instances with main instance
    val alignTables = dedupRemainingInstances.map{otherInstName => {
      val table = alignInstance(dedupMainInstanceName, dedupMainInstanceNodes, otherInstName, sg)
      otherInstName -> table
    }}.toMap
    // Propagate partition
    dedupRemainingInstances.foreach{otherInstName => {
      val mergesToConsider = dedupMainInstancePartitions.map{case (_, group) => {
        group.map(alignTables(otherInstName))
      }}.toSeq
      ap.perfomMergesIfPossible(mergesToConsider)

      // Save successful partitions
      dedupMainInstancePartitions.foreach{case (mainInstMergeId, members) => {
        val correspondingNodeId = alignTables(otherInstName)(members.head)
        val correspondingMergeId = ap.mg.idToMergeID(correspondingNodeId)
        dedupMergeIdMap(mainInstMergeId) += correspondingMergeId
      }}

    }}


    // 3. Unmerge?

    // Unsuccessful propagation: Partitions that doesn't apply to all dedup instances
    // Those partitions should work, but might be good to unmerge them to create larger partitions
    val unsuccesfulMergeIds = dedupMergeIdMap.values.filter(_.size < dedupInstances.size - 1).flatten.toSeq


    // Note: Optional: unmerge partitions that doesn't apply to all dedup instances
    val unmerge = true


    // 4. Apply original AP algorithm on remaining part of graph
    ap.partition(smallPartCutoff)

    convertIntoCPStmts(ap, excludedIDs.toSet)
    logger.info(partitioningQualityStats())

  }

  def getNumParts(): Int = sg.idToStmt count { _.isInstanceOf[CondPart] }

  def getPartInputMap(): Map[String,Seq[Int]] = {
    val allPartInputs = sg.validNodes.toSeq flatMap { id => sg.idToStmt(id) match {
      case cp: CondPart if !cp.alwaysActive => cp.inputs map { (_, cp.id) }
      case _ => Seq()
    }}
    Util.groupByFirst(allPartInputs)
  }

  def getPartOutputsToDeclare(): Seq[(String,Type)] = {
    val allPartOutputTypes = sg.idToStmt flatMap { _ match {
      case cp: CondPart => cp.outputsToDeclare.toSeq
      case _ => Seq()
    }}
    allPartOutputTypes
  }

  def getExternalPartInputNames(): Seq[String] = {
    val allPartInputs = (sg.idToStmt flatMap { _ match {
      case cp: CondPart => cp.inputs
      case _ => Seq()
    }}).toSet
    val allPartOutputs = (sg.idToStmt flatMap { _ match {
      case cp: CondPart => cp.outputsToDeclare.keys
      case _ => Seq()
    }}).toSet ++ alreadyDeclared.toSet
    (allPartInputs -- allPartOutputs).toSeq
  }

  def getExternalPartInputTypes(extIOtypes: Map[String, Type]): Seq[(String,Type)] = {
    getExternalPartInputNames() map {
      name => (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
    }
  }

  def partitioningQualityStats(): String = {
    val numParts = getNumParts()
    val partStmts = sg.idToStmt collect { case cp: CondPart => cp }
    val partSizes = partStmts map { cp => cp.memberStmts.size }
    val numStmtsTotal = partSizes.sum
    val numEdgesOrig = (partStmts flatMap {
        cp => cp.memberStmts flatMap { stmt => findDependencesStmt(stmt) map { _.deps.size }}
    }).sum
    val allOutputMaps = getPartInputMap()
    val numOutputsUnique = allOutputMaps.size
    val numOutputsFlat = (allOutputMaps map { _._2.size }).sum
    val percEdgesInParts = 100d * (numEdgesOrig - numOutputsFlat) / numEdgesOrig
    f"""|Parts: $numParts
        |Output nodes: $numOutputsUnique
        |Nodes in parts: $numStmtsTotal
        |Edges in parts: ${numEdgesOrig - numOutputsFlat} ($percEdgesInParts%2.1f%%))
        |Nodes/part: ${numStmtsTotal.toDouble/numParts}%.1f
        |Outputs/part: ${numOutputsUnique.toDouble/numParts}%.1f
        |Part size range: ${partSizes.min} - ${partSizes.max}""".stripMargin
  }
}

object MakeCondPart {
  def apply(ng: StatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) = {
    new MakeCondPart(ng, rn, extIOtypes)
  }
}
