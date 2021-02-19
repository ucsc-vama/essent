package essent

import essent.Graph.NodeID
import essent.Extract._
import essent.Util.{ExpressionUtils, StatementUtils, TraversableOnceUtils}
import essent.ir._
import firrtl.ir._
import _root_.logger._
import essent.Emitter.emitExpr
import essent.MakeCondPart.{ConnectionMap, InstanceAndConnectionMap, SignalTypeMap, getInstanceMemberName}
import firrtl.{MemKind, NodeKind, PortKind, RegKind, WRef, WireKind}

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

      // annotate the CondPart with the partition info if we have it
      var cpInfo:Info = NoInfo
      idToMemberStmts(id).head.foreachInfoRecursive {
        case i:GCSMInfo => cpInfo = i
        case _ => // ignore
      }

      val cpStmt = CondPart(cpInfo, topoOrder, alwaysActive, idToInputNames(id),
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
      val tempCPstmt = CondPart(NoInfo, newGroupID, true, Seq(), memberStmts, Map())
      sg.mergeStmtsMutably(newGroupID, matchingIDs diff Seq(newGroupID), tempCPstmt)
      Some(newGroupID)
    }
  }

  def doOpt(circuit: Circuit, smallPartCutoff: Int = 20) {
    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    excludedIDs ++= (sg.nodeRange filterNot sg.validNodes)
    val ap = AcyclicPart(sg, excludedIDs.toSet)
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
    }}).toSet ++ alreadyDeclared
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

  def doDedup(circuit: Circuit): DedupResult = {
    // find all CondParts per GCSM
    val condPartsPerGCSM = sg.idToStmt flatMap {
      case cp:CondPart if cp.gcsm.isDefined => Some(cp.gcsm.get -> cp)
      case _ => None
    } toMapOfLists

    // data structures to collect info about the GCSM CPs
    val signalTypeMap = mutable.Map[GCSMSignalReference, firrtl.ir.Type]()
    val mainGcsmSignalConnections = mutable.Map[GCSMSignalReference, WRef]() // maps the GCSM signal reference to the original one
    var placeholderNum = 0

    // take the first one and rewrite names
    //val allInstances = Extract.findAllModuleInstances(circuit).map(_.swap).toMap // prefix -> mod name
    val (mainGcsm, mainGcsmParts) = condPartsPerGCSM.head
    mainGcsmParts.foreach(cp => {
      // FUTURE - analyze the part flags
      val newCP = cp.copy(alwaysActive = true, gcsmConnectionMap = mainGcsmSignalConnections).mapStmt(stmt => {
        // check that the statement is valid
        stmt.mapExprRecursive {
          case w:WRef if (!rn.decLocal(w) || cp.outputsToDeclare.contains(w.name)) && Seq(NodeKind, PortKind, MemKind, RegKind, WireKind).contains(w.kind) => // reference to an external IO or another CP's value     /*if rn.decExtIO(w) || rn.isDec(w, PartOut) || rn.isDec(w, RegSet)*/
            // put a placeholder and fill in the first occurence since we're looking at it
            val newName = s"${mainGcsm.instanceName}_placeholder_${placeholderNum}"
            val ret = GCSMSignalReference(w.copy(name = newName), mainGcsm.instanceName)
            placeholderNum += 1

            signalTypeMap(ret) = rn.getSigType(w)
            mainGcsmSignalConnections(ret) = w
            ret
          case w:WRef if w.name.startsWith(mainGcsm.instanceName) && !rn.decLocal(w) => // name inside the GCSM, but local vars not needed
            val ret = GCSMSignalReference(w, mainGcsm.instanceName)
            signalTypeMap(ret) = rn.getSigType(w)
            mainGcsmSignalConnections(ret) = w
            ret
          case e => {
            e
          } // something else
        }
      }).asInstanceOf[CondPart]

      // Fixup outputs - change names if needed
      /*
      mainGcsmSignalConnections.map {
        case (gcsr, origRef) => newCP.outputsToDeclare.get(origRef.name) match {
          case Some(theType) => emitExpr(gcsr) -> theType // the new name
          case None =>
        }
      }*/

      // replace me in the SG as well
      val id = sg.idToStmt.indexOf(cp) // FIXME - there must be a better solution
      sg.idToStmt(id) = newCP
    })

    // Look at the other instances of the GCSM
    val tmp = Seq(getInstanceMemberName(mainGcsm) -> mainGcsmSignalConnections) ++ (condPartsPerGCSM.tail map {
      case (gcsmInfo, condPartsForInstance) =>
        placeholderNum = 0 // reset it
        val thisGcsmSignalConnections = mutable.Map[GCSMSignalReference, WRef]()

        // just like the main GCSM, iterate over each CP for this GCSM instance
        condPartsForInstance.foreach(cp => {
          // FUTURE - analyze the part flags
          val newCP = cp.copy(alwaysActive = true, gcsmConnectionMap = thisGcsmSignalConnections).mapStmt(stmt => {
            stmt.mapExprRecursive {
              case w:WRef if (!rn.decLocal(w) || cp.outputsToDeclare.contains(w.name)) && Seq(NodeKind, PortKind, MemKind, RegKind, WireKind).contains(w.kind) => // reference to an external IO or another CP's value     /*if rn.decExtIO(w) || rn.isDec(w, PartOut) || rn.isDec(w, RegSet)*/
                // put a placeholder and fill in the first occurence since we're looking at it
                val newName = s"${gcsmInfo.instanceName}_placeholder_${placeholderNum}"
                val ret = GCSMSignalReference(w.copy(name = newName), gcsmInfo.instanceName)
                placeholderNum += 1
                assert(rn.getSigType(w) == signalTypeMap(ret), "paradox! the type I see this time is not the same as in the main GCSM")
                thisGcsmSignalConnections(ret) = w
                ret
              case w:WRef if w.name.startsWith(gcsmInfo.instanceName) && !rn.decLocal(w) => // name inside the GCSM, but local vars not needed
                val ret = GCSMSignalReference(w, gcsmInfo.instanceName)
                assert(rn.getSigType(w) == signalTypeMap(ret), "paradox! the type I see this time is not the same as in the main GCSM")
                thisGcsmSignalConnections(ret) = w
                ret
              case e => e // something else
            }
          })

          // replace me in the SG as well
          val id = sg.idToStmt.indexOf(cp) // FIXME - there must be a better solution
          sg.idToStmt(id) = newCP // TODO - replace with EmptyStmt
        })

        getInstanceMemberName(gcsmInfo) -> thisGcsmSignalConnections
    })

    DedupResult(signalTypeMap, tmp)
  }
}

object MakeCondPart {
  type SignalTypeMap = collection.Map[GCSMSignalReference, firrtl.ir.Type]
  type ConnectionMap = collection.Map[GCSMSignalReference, WRef]
  type InstanceAndConnectionMap = (String, ConnectionMap) // FIXME - this is getting too complex

  def apply(ng: StatementGraph, rn: Renamer, extIOtypes: Map[String, Type]) = {
    new MakeCondPart(ng, rn, extIOtypes)
  }

  private def removeDots(s: String) = s.replace('.','$') // FIXME - copied from Renamer
  def getInstanceMemberName(gcsmInfo: GCSMInfo): String = s"instance_${removeDots(gcsmInfo.instanceName)}_"
}

// a little better than a tuple
case class DedupResult(typeMap: SignalTypeMap, placeholderMap: Seq[InstanceAndConnectionMap])