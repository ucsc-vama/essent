package essent

import _root_.logger._
import essent.Extract._
import essent.Graph.NodeID
import essent.MakeCondPart.{InstanceAndConnectionMap, SignalTypeMap, getInstanceMemberName}
import essent.Util.{IterableUtils, StatementUtils}
import essent.ir._
import firrtl.ir._
import firrtl.{MemKind, NodeKind, PortKind, RegKind, WRef, WireKind}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.reflect.ClassTag


class MakeCondPart(sg: TopLevelStatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) extends LazyLogging {
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

      // annotate the CondPart with the partition info if we have it
      val cpInfo = idToMemberStmts(id).head.getInfoByType[GCSMInfo]().getOrElse(NoInfo)

      val cpStmt = CondPart(cpInfo, topoOrder, alwaysActive, isRepeated = false, idToInputNames(id),
                                idToMemberStmts(id), outputsToDeclare.toMap)
      sg.mergeStmtsMutably(id, idToMemberIDs(id) diff Seq(id), cpStmt)
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
      val tempCPstmt = CondPart(NoInfo, newGroupID, alwaysActive = true, isRepeated = false, Seq(), memberStmts, Map())
      sg.mergeStmtsMutably(newGroupID, matchingIDs diff Seq(newGroupID), tempCPstmt)
      Some(newGroupID)
    }
  }

  def doOpt(circuit: Circuit, smallPartCutoff: Int = 20) {
    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)

    // analyze connectivity for the subgraphs corresponding to GCSM instances
    val ioForGcsm = sg.iterNodes.flatMap({
      case (id, inNeighs, outNeighs, prefix) if prefix.nonEmpty =>
        // find any nodes which have inputs and/or outputs outside the GCSM. these are the IO
        val a = if (outNeighs.exists(nid => sg.idToTag(nid) != prefix)) Some(prefix -> (Output, id)) else None
        val b = if (inNeighs.exists(nid => sg.idToTag(nid) != prefix)) Some(prefix -> (Input, id)) else None
        Seq(a, b).flatten
      case _ => Nil
    }).toMapOfLists

    def normalizeNodeName(prefix: String)(id: NodeID) = sg.idToName(id).stripPrefix(prefix)
    val constraints = ioForGcsm.map({
      case (prefix, ios) => {
        val (inputs, outputs) = ios.partition({ case (dir, _) => dir == Input })
        val inputIDs = inputs.map(_._2).toSet
        val constrsForInstance = outputs.flatMap({
          case (Output, outID) => sg.findExtPaths(outID, inputIDs).map(id =>
            normalizeNodeName(prefix)(outID) -> normalizeNodeName(prefix)(id)
          )
        }).toSet // output name -> Set of reachable inputs in this GCSM
        prefix -> constrsForInstance
      }
    })

    def isCompatible[K](sets: collection.Set[K]*): Boolean = sets
      .reduceLeft((a, b) => a.diff(b))
      .isEmpty
    val compatiblePartitionings = constraints.toStream.combinations(2).flatMap({
      case (inst1, inst1Constrs) +: (inst2, inst2Constrs) +: Stream.Empty =>
        // compute which set is the superset (if any)
        // if the constraints of X is a subset of Y, then since X has fewer constraints, Y can be used to partition X
        // (and vice-versa)
        val a = if (inst1Constrs.subsetOf(inst2Constrs)) Some(inst2 -> inst1) else None
        val b = if (inst2Constrs.subsetOf(inst1Constrs)) Some(inst1 -> inst2) else None
        Seq(a, b).flatten
    }).toIterable.toMapOfLists // instanceName -> is compatible with these other instance partitionings
    val chosenPartitioning = compatiblePartitionings.maxBy({ case (_, compatInsts) => compatInsts.size })

    // perform partitioning
    val ap = AcyclicPart(sg, excludedIDs.toSet)
    ap.partition(smallPartCutoff)

    // look at connectivity to determine compatibility
    //val gcsmInstanceToGroups = ap.mg.groupsByTag().filterKeys(_.nonEmpty)

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

  def doDedup(circuit: Circuit): DedupResult = {
    // if no deduplication possible, just return nothing
    if (!sg.hasGCSM) return DedupResult(Map.empty, Seq.empty)

    // first we have to tweak the partitioning to match the parent's
    fixupPartitioning()

    // find all CondParts for this GCSM
    val foundGCSMs = sg.idToStmt.collect({
      case cp: CondPart if cp.gcsm.isDefined => cp.gcsm.get.instanceName -> cp
    }).toMapOfLists
    assert(foundGCSMs.size == sg.gcsmInstances.size, "differing number of GCSM instances")
    //assert(maybeGCSM.size == 1, "multiple GCSMs identified which is not supported")
    //assert(maybeGCSM.head._1.instanceName == sg.gcsmInstances.head, "the found GCSM is not correct")

    // data structures to collect info about the GCSM CPs
    val signalTypeMap = mutable.Map[GCSMSignalReference, firrtl.ir.Type]()
    val mainGcsmSignalConnections = mutable.Map[GCSMSignalReference, WRef]() // maps the GCSM signal reference to the original one
    var placeholderNum = 0

    // take the first one and rewrite names
    //val allInstances = Extract.findAllModuleInstances(circuit).map(_.swap).toMap // prefix -> mod name
    val mainGcsm = sg.gcsmInstances.head
    val mainGcsmParts = foundGCSMs(mainGcsm)
    val mainGcsmPartsNew = mainGcsmParts.map(cp => {
      // FUTURE - analyze the part flags
      val newCP = cp.copy(alwaysActive = true, gcsmConnectionMap = mainGcsmSignalConnections).mapStmt(stmt => {
        // check that the statement is valid
        stmt.mapExprRecursive {
          case w:WRef if (!rn.decLocal(w) || cp.outputsToDeclare.contains(w.name)) && Seq(NodeKind, PortKind, MemKind, RegKind, WireKind).contains(w.kind) => // reference to an external IO or another CP's value     /*if rn.decExtIO(w) || rn.isDec(w, PartOut) || rn.isDec(w, RegSet)*/
            // put a placeholder and fill in the first occurence since we're looking at it
            val newName = s"${mainGcsm}_placeholder_${placeholderNum}"
            val ret = GCSMSignalReference(w.copy(name = newName), mainGcsm)
            placeholderNum += 1

            signalTypeMap(ret) = rn.getSigType(w)
            mainGcsmSignalConnections(ret) = w
            ret
          case w:WRef if w.name.startsWith(mainGcsm) && !rn.decLocal(w) => // name inside the GCSM, but local vars not needed
            val ret = GCSMSignalReference(w, mainGcsm)
            signalTypeMap(ret) = rn.getSigType(w)
            mainGcsmSignalConnections(ret) = w
            ret
          case e => {
            e
          } // something else
        }
      }).asInstanceOf[CondPart]

      // replace me in the SG as well
      val id = sg.idToStmt.indexOf(cp) // FIXME - there must be a better solution
      sg.idToStmt(id) = newCP
      newCP
    })

    // Look at the other instances of the GCSM
    val signalConnections = Seq(getInstanceMemberName(mainGcsm) -> mainGcsmSignalConnections) ++
      sg.gcsmInstances.tail.map { otherGcsm =>
        val newConnections = mainGcsmSignalConnections flatMap { case (gcsmSigRef, origWRef) =>
          // rewrite the origWRef to replace the prefix with my prefix, check if that name exists in SG
          // if so, output this rewrite
          val newName = rewriteSignalName(origWRef.name, otherGcsm)
          if (sg.nameToID.contains(newName)) {
            Some(gcsmSigRef.copy(gcsmInstanceName = otherGcsm) -> origWRef.copy(name = newName))
          } else {
            None
          }
        }

        // set CondParts to be repeated
        foundGCSMs(otherGcsm).foreach { cp =>
          sg.idToStmt(sg.idToStmt.indexOf(cp)) = cp.copy(isRepeated = true, alwaysActive = true)
        }

        getInstanceMemberName(otherGcsm) -> newConnections
      }

    DedupResult(signalTypeMap, signalConnections)
  }

  private def fixupPartitioning(): Unit = {
    val cpPerGcsm = sg.idToStmt.zipWithIndex.collect({
      case (cp: CondPart, id) if cp.gcsm.isDefined => cp.gcsm.get.instanceName -> (cp, id)
    }).toMapOfLists

    val okCPs = (cpPerGcsm(sg.gcsmInstances.head).flatMap { case (mainCp, tmpId) =>
      sg.gcsmInstances.tail.map { otherInstance =>
        val inputs = mainCp.inputs.map(rewriteSignalName1(otherInstance)).filter(sg.nameToID.contains)
        val outputs1 = mainCp.outputsToDeclare.map({
          case (name, tpe) => (rewriteSignalName(name, otherInstance), tpe)
        })
        val outputs = outputs1.filterKeys(sg.nameToID.contains)
        val tmp123 = s"mainCp: $tmpId"
        val tmp456 = sg.idToName(tmpId)
        val newCP = CondPart(info = GCSMInfo("", otherInstance),
          id = mainCp.id,
          alwaysActive = true,
          isRepeated = true,
          inputs = inputs,
          outputsToDeclare = outputs,
          memberStmts = Seq(),
          gcsmConnectionMap = Map.empty)

        // insert that into the SG
        //val newID = sg.getID(outputs.headOption.get)
        val newOutputName =
          if (outputs.isEmpty) s"CondPartNoOutputs_${mainCp.id}_${otherInstance}"
          else outputs.head._1
        val newID = sg.getID(newOutputName)
        outputs.drop(1).foreach { case (name, _) => sg.nameToID(name) = newID }
        sg.idToStmt(newID) = newCP
        sg.idToName(newID) = newOutputName
        sg.nameToID(newOutputName) = newID
        sg.validNodes += newID
        sg.markGCSMInfo(newID)(newCP.info)

        // add edges
        val xyz2683 = sg.idToStmt(2683)
        val xyz528 = sg.idToStmt(528)
        val xyz2653 = sg.idToStmt(2653)
        inputs.foreach(name => {
          val thatID = sg.getID(name)
          //if (thatID == newID) return // don't make cycle to myself
          sg.addEdge(thatID, newID)
          val p1exists = sg.extPathExists(528, 2683)
          val p1exists1 = sg.extPathExists(2683, 528)
          val p2exists = sg.extPathExists(2683, 2653)
          val p2exists2 = sg.extPathExists(2653, 2683)
          val p3exists = sg.extPathExists(2653, 528)
          val p3exists1 = sg.extPathExists(528, 2653)
          val tmpAfter = TopologicalSort(sg)
        })

        outputs.foreach { case (name, _) =>
          val thatID = sg.getID(name)
          //if (thatID == newID) return // don't make a cycle to myself

          // find other nodes using this output of newCP. then add a new edge from that node to this one
          sg.inNeigh.zipWithIndex.foreach {
            case (list, id) if list.contains(thatID) => {
              sg.addEdge(newID, id)
              val tmpAfter = TopologicalSort(sg)
            }
            case _ => // ignore
          }
        }

        // update renamer
        (outputs.keySet -- alreadyDeclared) foreach { name =>
          rn.mutateDecTypeIfLocal(name, PartOut)
          rn.addPartCache(name + cacheSuffix, rn.nameToMeta(name).sigType)
        }

        newID
      }
    }).toSet

    // remove the old CondParts for the other GCSMs
    cpPerGcsm.foreach {
      case (instanceName, condParts) if sg.gcsmInstances.tail.contains(instanceName) => condParts foreach { case (cp, idX) =>
        //val id = sg.idToStmt.indexOf(cp)
        if (!okCPs.contains(idX)) {
          sg.idToStmt(idX) = EmptyStmt
          sg.validNodes -= idX
        }
      }
      case _ => // ignore
    }
  }
}

object MakeCondPart {
  type SignalTypeMap = collection.Map[GCSMSignalReference, firrtl.ir.Type]
  type ConnectionMap = collection.Map[GCSMSignalReference, WRef]
  type InstanceAndConnectionMap = (String, ConnectionMap) // FIXME - this is getting too complex

  def apply(ng: TopLevelStatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) = {
    new MakeCondPart(ng, rn, extIOtypes)
  }

  private def removeDots(s: String) = s.replace('.','$') // FIXME - copied from Renamer
  def getInstanceMemberName(gcsmInfo: GCSMInfo): String = getInstanceMemberName(gcsmInfo.instanceName)
  def getInstanceMemberName(instanceName: String): String = s"instance_${removeDots(instanceName)}_"
}

// a little better than a tuple
case class DedupResult(typeMap: SignalTypeMap, placeholderMap: Seq[InstanceAndConnectionMap])