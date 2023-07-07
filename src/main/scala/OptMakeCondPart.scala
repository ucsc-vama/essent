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
      val isAcyclic = sg.mergeIsAcyclic(idToMemberIDs(id).toSet)
      if (!isAcyclic) {
        println(s"Cycle detected, topoOrder ${topoOrder}, mergeId ${id}")
        println(s"Merge ${idToMemberIDs(id).size} nodes")
      }
      assert(isAcyclic)
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
    val dedupMainInstanceNodes = modInstInfo.instInclusiveNodesTable(dedupMainInstanceName).toSet
    val dedupRemainingInstances = dedupInstances.filter(_ != dedupMainInstanceName)

    // Table that stores corresponding mergeIDs
    val dedupMergeIdMap = mutable.HashMap[Int, mutable.ArrayBuffer[NodeID]]()


    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)

    // 1. Only partition nodes for main dedup instqance
    var startTime = System.currentTimeMillis()
    logger.info("Start initial partitioning for main dedup module")
    val excludeIDsForDedup1 = excludedIDs.clone() ++ sg.nodeRange().filterNot(dedupMainInstanceNodes.contains)
    var ap = AcyclicPart(sg, excludeIDsForDedup1.toSet)
    ap.partition(smallPartCutoff)

    var stopTime = System.currentTimeMillis()
    logger.info(s"Took ${stopTime - startTime} ms for initial partitioning")

    // Check merge graph size
    var max_partition_size = ap.mg.mergeIDToMembers.values.map(_.size).max
    logger.info(s"After initial partition, max partition size is ${max_partition_size}")


    startTime = System.currentTimeMillis()
    // Collect partition result
    // Note: Only record members, as after multiple merge (AcyclicPart), mergeId may not be head of group
    val dedupMainInstancePartitionMembers = ArrayBuffer[Seq[NodeID]]()

    ap.mg.mergeIDToMembers.foreach{case (mergeId, members) => {
      // For all merges (more than 1 members), they should within main dedup inst
      //   as limited by excludeIDsForDedup1
      if (members.size > 1) {
        // Only save internal partitions (no outside connection)
        val groupHasOutsideConnection = members.flatMap{nid => {
          (sg.inNeigh(nid) ++ sg.outNeigh(nid)).map{!dedupMainInstanceNodes.contains(_)}
        }}.reduce(_|_)
        if ((!groupHasOutsideConnection)){
          dedupMainInstancePartitionMembers += members
        }
      }
    }}



    stopTime = System.currentTimeMillis()
    logger.info(s"Took ${stopTime - startTime} ms for collecting initial partition result")

    // 2. Plan for partitioning propagation from main instance to other dedup instances
    // Only cares partitions that are internal to main instance

    // Align remaining dedup instances with main instance
    val alignTables = dedupRemainingInstances.map{otherInstName => {
      val table = alignInstance(dedupMainInstanceName, dedupMainInstanceNodes.toSeq, otherInstName, sg)
      otherInstName -> table
    }}.toMap

    // Propagation plan
    val dedupPropagationPlan = dedupRemainingInstances.map{otherInstName => {
      val otherInstMerges = dedupMainInstancePartitionMembers.map{group => {
        group.map(alignTables(otherInstName))
      }}.toSeq
      otherInstName -> otherInstMerges
    }}.toMap



    // 4. Recover dedup instances
    ap = AcyclicPart(sg, excludedIDs.toSet)
    // Recover main inst
    val completedMerges = ap.perfomMergesIfPossible(dedupMainInstancePartitionMembers)
    // Assert: every group in main instance are merged
    assert(dedupMainInstancePartitionMembers.size == completedMerges.size)

    // Get mergeids
    val dedupMainInstancePartitions = mutable.HashMap[NodeID, Seq[NodeID]]()
    dedupMainInstancePartitionMembers.foreach{members => {
      val headMember = members.head
      val mergeId = ap.mg.idToMergeID(headMember)

      // Just curious. This doesn't need to be true
      assert(mergeId == headMember)

      dedupMainInstancePartitions(mergeId) = members
    }}

    // Init
    dedupMainInstancePartitions.keys.foreach{mid => {
      dedupMergeIdMap(mid) = new ArrayBuffer[NodeID]()
    }}


    val numPartsInMain = dedupMainInstancePartitionMembers.size
    val numNodesInMain = dedupMainInstancePartitions.keys.map(ap.mg.mergeIDToMembers).map(_.size).sum
    println(s"Average size of partition in main instance is ${numNodesInMain.toFloat / numPartsInMain}")

    // Check merge graph size
    max_partition_size = ap.mg.mergeIDToMembers.values.map(_.size).max
    logger.info(s"After propagate initial partition, max partition size is ${max_partition_size}")


    logger.info("Propagating initial partition result to other instances")
    // Propagate partition
    dedupRemainingInstances.indices.foreach{instId => {
      val otherInstName = dedupRemainingInstances(instId)

      val mergesToConsider = dedupPropagationPlan(otherInstName)
      val completedMerges = ap.perfomMergesIfPossible(mergesToConsider)
      // Assert: every group is merged
      assert(mergesToConsider.size == completedMerges.size)

      // Save partitions
      dedupMainInstancePartitions.foreach{case (mainInstMergeId, members) => {
        val correspondingNodeId = alignTables(otherInstName)(members.head)
        val correspondingMergeId = ap.mg.idToMergeID(correspondingNodeId)
        dedupMergeIdMap(mainInstMergeId) += correspondingMergeId
      }}
    }}


    // TODO: Double check nodes not in dedup are never merged

    // Check merge graph size
    max_partition_size = ap.mg.mergeIDToMembers.values.map(_.size).max
    logger.info(s"After propagate partition, max partition size is ${max_partition_size}")


    logger.info(s"${dedupMergeIdMap.size} partitions in main dedup instance propagated to ${dedupInstances.size - 1} instances.")

    val excludeIDsForFinalPhase = (excludedIDs ++ dedupMainInstancePartitionMembers.flatten ++ dedupPropagationPlan.values.flatten.flatten).toSet
    ap = new AcyclicPart(ap.mg, excludeIDsForFinalPhase)
    ap.partition(smallPartCutoff)

//    dedupRemainingInstances.indices.foreach{instId => {
//      val otherInstName = dedupRemainingInstances(instId)
//
//      val numParts = dedupPropagationPlan(otherInstName).size
//      val numNodes = dedupMainInstancePartitions.keys.map(dedupMergeIdMap).map(_(instId)).map(ap.mg.mergeIDToMembers).map(_.size).sum
//      println(s"Before partitioning, Average size of partition in instance ${otherInstName} is ${numNodes.toFloat / numParts}")
//    }}


//    dedupRemainingInstances.indices.foreach{instId => {
//      val otherInstName = dedupRemainingInstances(instId)
//
//      // Search for new id
//      val partitions = dedupPropagationPlan(otherInstName)
//      val mergeIds = partitions.map {members => {
//        ap.mg.idToMergeID(members.head)
//      }}
//
//      val numParts = partitions.size
//      val numNodes = mergeIds.map(ap.mg.mergeIDToMembers).map(_.size).sum
//      println(s"After partitioning, Average size of partition in instance ${otherInstName} is ${numNodes.toFloat / numParts}")
//    }}



    // Check merge graph size
    max_partition_size = ap.mg.mergeIDToMembers.values.map(_.size).max
    logger.info(s"After final partition, max partition size is ${max_partition_size}")

    TopologicalSort(ap.mg)



//    // Test
//    dedupRemainingInstances.indices.foreach{idx => {
//      val instName = dedupRemainingInstances(idx)
//      val mainInstMergeIds = dedupMainInstancePartitions.keys
//      val numPartsInInst = mainInstMergeIds.size
//      val numNodesInInst = mainInstMergeIds.map(dedupMergeIdMap).map(_(idx)).map(ap.mg.mergeIDToMembers).map(_.size).sum
//      println(s"Average size of partition in instance ${instName} is ${numNodesInInst.toFloat / numPartsInInst}")
//    }}
//
    // Test
    val numParts = ap.mg.mergeIDToMembers.size
    val numNodes = ap.mg.mergeIDToMembers.values.map(_.size).sum
    println(s"Average size of partition is ${numNodes.toFloat / numParts}")


    convertIntoCPStmts(ap, excludedIDs.toSet)

    TopologicalSort(sg)
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
