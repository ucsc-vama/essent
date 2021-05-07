package essent

import _root_.logger._
import essent.Emitter.emitExpr
import essent.Extract._
import essent.Graph.NodeID
import essent.MakeCondPart.ConnectionMap
import essent.Util.{IterableUtils, MapUtils, StatementUtils}
import essent.ir._
import firrtl.ir._
import firrtl.{Flow, Kind, MemKind, NodeKind, PortKind, RegKind, WRef, WSubAccess, WSubField, WireKind}

import scala.collection.mutable
import scala.language.postfixOps
import scala.reflect.ClassTag


class MakeCondPart(sg: StatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) extends LazyLogging {
  val cacheSuffix = "$old"

  val alreadyDeclared = sg.stateElemNames().toSet

  def convertIntoCPStmts(ap: AcyclicPart, excludedIDs: collection.Set[NodeID]) {
    val idToMemberIDs = ap.iterParts
    val idToMemberStmts = (idToMemberIDs map { case (id, members) => {
      val memberStmts = sg.idToStmt(id) match {
        case cp: CondPart => cp.memberStmts
        case _ => members map sg.idToStmt
      }
      (id -> memberStmts)
    }}).toMap
    val idToProducedOutputs = idToMemberStmts mapValues { _ flatMap findResultName toSet }
    val idToInputNames = idToMemberStmts map { case (id, memberStmts) => {
      val partDepNames = memberStmts flatMap findDependencesStmt flatMap { _.deps }
      val externalDepNames = partDepNames.toSet -- (idToProducedOutputs(id) -- alreadyDeclared)
      (id -> externalDepNames)
    }}
    val allInputs = idToInputNames.values.flatten.toSet
    val validParts = (idToMemberIDs flatMap { case (id, members) => {
      if (members.exists(sg.validNodes)) Seq(id)
      else Seq()
    }}).toSet
    val partsTopoSorted = TopologicalSort(ap.mg) filter validParts
    partsTopoSorted.zipWithIndex foreach { case (id, topoOrder) => {
      val consumedOutputs = idToProducedOutputs(id).intersect(allInputs)
      val namesToDeclare = consumedOutputs -- alreadyDeclared
      val nameToStmts = idToMemberStmts(id) map { stmt => (findResultName(stmt) -> stmt) }
      val outputsToDeclare = nameToStmts collect {
        case (Some(name), stmt) if namesToDeclare.contains(name) => (name -> findResultType(stmt))
      }
      val alwaysActive = excludedIDs.contains(id)

      // check that partitioning worked correctly
      val memberIDs = idToMemberIDs(id).toSet
      assert(memberIDs.intersect(excludedIDs).isEmpty || memberIDs.subsetOf(excludedIDs), "incorrect partitioning!")

      // annotate the CondPart with the partition info if we have it
      val cpInfo = idToMemberStmts(id).head.getInfoByType[GCSMInfo]().getOrElse(NoInfo)

      val cpStmt = CondPart(cpInfo, topoOrder, alwaysActive, isRepeated = false, idToInputNames(id),
                                idToMemberStmts(id), outputsToDeclare.toMap)
      sg.mergeStmtsMutably(id, idToMemberIDs(id) diff Seq(id), cpStmt)
      //TopologicalSort(sg) // TODO debug
      namesToDeclare foreach { name =>
        rn.mutateDecTypeIfLocal(name, PartOut)
        rn.addPartCache(name + cacheSuffix, rn.nameToMeta(name).sigType)
      }
      assert(sg.validNodes(id))
    }}
    val externalInputs = getExternalPartInputTypes(extIOtypes)
    externalInputs foreach {
      case (name, tpe) => rn.addPartCache(name + cacheSuffix, tpe)
    }
  }

  /**
   * Take all the statements of a given type and merge them together into an always-active [[CondPart]] which replaces
   * the first occurence of that statement type
   * @param tag
   * @tparam T
   * @return The ID of the clump, or None if there wasn't any of that kind in the graph
   */
  def clumpByStmtType[T <: Statement]()(implicit tag: ClassTag[T]): Option[Int] = {
    val matchingIDs = sg.idToStmt.zipWithIndex collect { case (t: T, id: Int) => id }
    if (matchingIDs.isEmpty) None
    else {
      val newGroupID = matchingIDs.min
      val memberStmts = matchingIDs map sg.idToStmt
      val tempCPstmt = CondPart(NoInfo, newGroupID, alwaysActive = true, isRepeated = false, Set(), memberStmts, Map())
      sg.mergeStmtsMutably(newGroupID, matchingIDs diff Seq(newGroupID), tempCPstmt)
      Some(newGroupID)
    }
  }

  def doOpt(smallPartCutoff: Int = 20): DedupResult = {
    val excludedIDs = mutable.Set[NodeID]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)

    // analyze connectivity for the subgraphs corresponding to GCSM instances
    trait GCSMNodeType
    case object GCSMInputNode extends GCSMNodeType
    case object GCSMOutputNode extends GCSMNodeType
    case object GCSMInternalNode extends GCSMNodeType
    def isNodeExternalToPrefix(prefix: String)(nid: NodeID) = sg.idToTag(nid) != prefix
    val ioForGcsm = sg.iterNodes.flatMap({
      case (id, inNeighs, outNeighs, prefix) if prefix.nonEmpty =>
        // find any nodes which have inputs and/or outputs outside the GCSM. these are the IO
        def accept(tpe: GCSMNodeType) = prefix -> (tpe, id)
        val maybeIn       = if (inNeighs.exists(isNodeExternalToPrefix(prefix))) Some(accept(GCSMInputNode)) else None
        val maybeOut      = if (outNeighs.exists(isNodeExternalToPrefix(prefix))) Some(accept(GCSMOutputNode)) else None
        val maybeInternal = if (maybeIn.isEmpty && maybeOut.isEmpty) Some(accept(GCSMInternalNode)) else None
        Seq(maybeIn, maybeOut, maybeInternal).flatten
      case _ => Nil
    }).toMapOfLists.mapValues(_.toSet)

    // determine constraints: the pairs of (output name -> input name) that are combinationally
    // reachable through the rest of the design, for each instance
    def normalizeNodeName(prefix: String)(id: NodeID) = sg.idToName(id).stripPrefix(prefix)
    val constraints = ioForGcsm.map({
      case (prefix, ios) => {
        val iosMap = ios.toMapOfLists.mapValues(_.toSet)
        val excludeNodes = iosMap(GCSMInternalNode) ++ (iosMap(GCSMOutputNode) -- iosMap(GCSMInputNode)) // don't take nodes that are internal, or other outputs which aren't inputs
        val constrsForInstance = iosMap(GCSMOutputNode).flatMap({ outID =>
          sg.findExtPaths(outID, iosMap(GCSMInputNode), excludeNodes).map(id => {
            val srcName = normalizeNodeName(prefix)(outID)
            val destName = normalizeNodeName(prefix)(id)
            val tmpStmt = sg.idToStmt(id)
            srcName -> destName
          })
        }) // output name -> Set of reachable inputs in this GCSM
        prefix -> constrsForInstance
      }
    })

    // find compatible partitionings
    val compatiblePartitionings = constraints.toStream.combinations(2).flatMap({
      case (inst1, inst1Constrs) +: (inst2, inst2Constrs) +: Stream.Empty =>
        // compute which set is the superset (if any)
        // if the constraints of X is a subset of Y, then since X has fewer constraints, Y can be used to partition X
        // (and vice-versa)
        val a = if (inst1Constrs.subsetOf(inst2Constrs)) Some(inst2 -> inst1) else None
        val b = if (inst2Constrs.subsetOf(inst1Constrs)) Some(inst1 -> inst2) else None
        Seq(a, b).flatten
    }).toIterable.toMapOfLists.mapValues(_.toSet) // instanceName -> is compatible with these other instance partitionings

    // pick the partitioning with the largest number of compatible instances
    // FUTURE: if there are several groups of incompatible partitionings, handle multiple
    val chosenPartitioning = compatiblePartitionings.maxBy({ case (_, compatInsts) => compatInsts.size })

    // Partitioning phase 1: Only the nodes of the chosen instance of the GCSM
    val firstInstanceNodes = ioForGcsm(chosenPartitioning._1).map(_._2)
    val gcsmExcludeNodes = sg.nodeRange().diff(firstInstanceNodes.toSeq) // all nodes except those of the chosen instance
    var ap = AcyclicPart(sg, excludedIDs ++ gcsmExcludeNodes)
    //TopologicalSort(ap.mg) // TODO debug
    ap.partition(smallPartCutoff)
    //TopologicalSort(ap.mg) // TODO debug

    // Partitioning phase 1.5: re-allow all the nodes so we can apply the partitioning
    ap = new AcyclicPart(ap.mg, excludedIDs)

    // find the partitioning of the main instance and apply to redundant ones
    val otherInstanceResults = for {
      (macroID, memberIDs) <- ap.iterParts().toSeq // for each group in the main instance
      if ap.mg.idToTag(macroID) == chosenPartitioning._1 // filter to only be main GCSM things
      redundantInstance <- chosenPartitioning._2 // for each redundant instance
    } yield {
      val redundantNodesForInstance = ioForGcsm(redundantInstance).map({
        case (_, id) => normalizeNodeName(redundantInstance)(id) -> id
      }).toMap // FIXME - this can be hoisted outside the loop
      val namesForMainPartition = memberIDs.map({ id =>
        normalizeNodeName(chosenPartitioning._1)(id)
      }).toSet

      // find the equivalent macroID for the redundant instance
      val macroNameForRedundant = normalizeNodeName(chosenPartitioning._1)(macroID)
      val macroIDForRedundant = redundantNodesForInstance(macroNameForRedundant)

      // line up the equivalent nodes
      val nodesToMerge = Seq(macroIDForRedundant) ++ namesForMainPartition.collect({
        case name if name != macroNameForRedundant => redundantNodesForInstance(name)
      })

      if (nodesToMerge.size > 1) {
        //ap.mg.saveAsGEXF("pre-merge.gexf", sg.tmpIdToString)
        //val mergeResult = ap.perfomMergesIfPossible(nodesToMerge.toSeq) // nodesToMerge.toSeq
        val mergeResult = ap.perfomMergesIfPossible(Seq(nodesToMerge)) // nodesToMerge.toSeq
        //TopologicalSort(ap.mg) // TODO debug
        println(mergeResult)
        assert(mergeResult.nonEmpty, "failed to merge!")
      }

      // return the mapping
      macroID -> macroIDForRedundant
    }
    val mainIDToRedundants = otherInstanceResults.toMapOfLists

    // Partitioning phase 2: all other nodes, except the GCSM ones
    ap = new AcyclicPart(ap.mg, excludedIDs ++ firstInstanceNodes ++ mainIDToRedundants.values.flatten)
    ap.partition(smallPartCutoff)
    //TopologicalSort(ap.mg) // TODO debug
    //ap.mg.saveAsGEXF("post-partition.gexf", sg.tmpIdToString) // TODO - remove

    // convert to CondParts
    convertIntoCPStmts(ap, excludedIDs)
    logger.info(partitioningQualityStats())
    //sg.saveAsGEXF("after-convert-to-cp.gexf")

    // rewrite the main CondPart to make it general and accept the various connections
    val nameToPlaceholderMap = mutable.Map[String, GCSMSignalReference]()
    var placeholderNum = 0

    def isUsefulRefKind(k: Kind) = k match {
      case NodeKind | PortKind | MemKind | RegKind | WireKind => true
      case _ => false
    }
    def getGcsmPlaceholder(name: String, tpe: firrtl.ir.Type, flow: Flow): Option[GCSMSignalReference] = {
      val newName = name.stripPrefix(chosenPartitioning._1)
      if (sg.nameToID.contains(name) && !rn.decLocal(name)) {
        Some(nameToPlaceholderMap.getOrElseUpdate(newName, {
          val n = GCSMSignalReference(s"GCSMPLACEHOLDER_${placeholderNum}_", tpe, flow)
          placeholderNum += 1
          n
        }))
      } else None
    }
    def rewriteNames(expr: Expression): Expression = (expr match {
      case w: WRef if isUsefulRefKind(w.kind) => getGcsmPlaceholder(w.name, w.tpe, w.flow)
      case w: WSubField => getGcsmPlaceholder(emitExpr(w)(null), w.tpe, w.flow)
      case _ => None
    }).getOrElse(expr.mapExpr(rewriteNames)) // FIXME - ensure that no GCSM signals can slip thru the cracks

    mainIDToRedundants foreach { case (macroID, redundants) =>
      sg.idToStmt(macroID) = sg.idToStmt(macroID) match {
        case macroCP: CondPart => {
          // rewrite statements
          val newCP = macroCP.copy(alwaysActive = true).mapStmt(stmt => {
            stmt.mapExpr(rewriteNames)
          })

          // update the redundant CPs
          redundants foreach { otherID =>
            // replace CondPart
            sg.idToStmt(otherID) = sg.idToStmt(otherID).asInstanceOf[CondPart]
              .copy(id = macroCP.id, alwaysActive = true, isRepeated = true)
          }

          newCP
        }
        case s => s
      }
    }

    DedupResult(Set(chosenPartitioning._1) ++ chosenPartitioning._2, nameToPlaceholderMap)
  }

  def getNumParts(): Int = sg.idToStmt count { _.isInstanceOf[CondPart] }

  def getPartInputMap(): collection.Map[String, Seq[Int]] = {
    sg.validNodes.flatMap { id => sg.idToStmt(id) match {
      case cp: CondPart if !cp.alwaysActive => cp.inputs map { (_, cp.id) }
      case _ => Seq()
    }} toMapOfLists
  }

  def getPartOutputsToDeclare(): Seq[(String,Type)] = {
    val allPartOutputTypes = sg.idToStmt flatMap { _ match {
      case cp: CondPart => cp.outputsToDeclare.toSeq
      case _ => Seq()
    }}
    allPartOutputTypes
  }

  def getExternalPartInputNames(): Set[String] = {
    val allPartInputs = (sg.idToStmt flatMap {
      case cp: CondPart => cp.inputs
      case _ => Seq()
    }).toSet
    val allPartOutputs = (sg.idToStmt flatMap {
      case cp: CondPart => cp.outputsToDeclare.keys
      case _ => Set()
    }).toSet
    val ret = allPartInputs -- (allPartOutputs ++ alreadyDeclared)
    ret
  }

  def getExternalPartInputTypes(extIOtypes: Map[String, Type]): Iterable[(String,Type)] = {
    val extPartInputNames = getExternalPartInputNames()
    val tmp = extPartInputNames.diff(extIOtypes.keySet)
    extPartInputNames map {
      name => {
        (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
      }
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

  def getInstanceMemberName(gcsmInfo: GCSMInfo): String = getInstanceMemberName(gcsmInfo.instanceName)
  def getInstanceMemberName(instanceName: String): String = s"instance_${rn.removeDots(instanceName)}_"

  /**
   * Holds the instances for the GCSM and their placeholder signals
   */
  case class DedupResult private(instances: Set[String], placeholderMap: ConnectionMap)
}

object MakeCondPart {
  type ConnectionMap = collection.Map[String, GCSMSignalReference]

  def apply(ng: StatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) = {
    new MakeCondPart(ng, rn, extIOtypes)
  }
}
