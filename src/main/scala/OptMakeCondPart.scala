package essent

import essent.BareGraph.NodeID
import essent.Extract._
import essent.ir._

import firrtl.ir._

import collection.mutable.ArrayBuffer
import scala.reflect.ClassTag


// TODO: cutoff parameter
// TODO: compact emitted range IDs

class MakeCondPart(ng: NamedGraph) {
  val alreadyDeclared = ng.stateElemNames().toSet

  def convertIntoAZStmts(ap: AcyclicPart, excludedIDs: Set[NodeID]) {
    val idToMemberIDs = ap.iterParts
    val idToMemberStmts = (idToMemberIDs map { case (id, members) => {
      val memberStmts = ng.idToStmt(id) match {
        case az: ActivityZone => az.memberStmts
        case _ => members map ng.idToStmt
      }
      (id -> memberStmts)
    }}).toMap
    val idToProducedOutputs = idToMemberStmts mapValues { _ flatMap findResultName }
    val idToInputNames = idToMemberStmts map { case (id, memberStmts) => {
      val zoneDepNames = memberStmts flatMap findDependencesStmt flatMap { _.deps }
      val externalDepNames = zoneDepNames.toSet -- (idToProducedOutputs(id).toSet -- alreadyDeclared)
      (id -> externalDepNames.toSeq)
    }}
    val allInputs = idToInputNames.values.flatten.toSet
    val partsTopoSorted = TopologicalSort(ng) filter idToMemberIDs.keys.toSet
    partsTopoSorted.zipWithIndex foreach { case (id, azIndex) => {
      val consumedOutputs = idToProducedOutputs(id).toSet.intersect(allInputs)
      val namesToDeclare = consumedOutputs -- alreadyDeclared
      val nameToStmts = idToMemberStmts(id) map { stmt => (findResultName(stmt) -> stmt) }
      val outputsToDeclare = nameToStmts collect {
        case (Some(name), stmt) if namesToDeclare.contains(name) => (name -> findResultType(stmt))
      }
      val alwaysActive = excludedIDs.contains(id)
      val azStmt = ActivityZone(azIndex, alwaysActive, idToInputNames(id), idToMemberStmts(id), outputsToDeclare.toMap)
      ng.mergeStmtsMutably(id, idToMemberIDs(id) diff Seq(id), azStmt)
    }}
  }

  def clumpByStmtType[T <: Statement]()(implicit tag: ClassTag[T]): Option[Int] = {
    val matchingIDs = ng.idToStmt.zipWithIndex collect { case (t: T, id: Int) => id }
    if (matchingIDs.isEmpty) None
    else {
      val newGroupID = matchingIDs.min
      val memberStmts = matchingIDs map ng.idToStmt
      val tempAZstmt = ActivityZone(newGroupID, true, Seq(), memberStmts, Map())
      ng.mergeStmtsMutably(newGroupID, matchingIDs diff Seq(newGroupID), tempAZstmt)
      Some(newGroupID)
    }
  }

  def doOpt() {
    val excludedIDs = ArrayBuffer[Int]()
    clumpByStmtType[Print]() foreach { excludedIDs += _ }
    val ap = AcyclicPart(ng, excludedIDs.toSet)
    convertIntoAZStmts(ap, excludedIDs.toSet)
  }

  def getNumZones(): Int = ng.idToStmt count { _.isInstanceOf[ActivityZone] }

  def getZoneInputMap(): Map[String,Seq[Int]] = {
    val allZoneInputs = ng.validNodes.toSeq flatMap { id => ng.idToStmt(id) match {
      case az: ActivityZone if !az.alwaysActive => az.inputs map { (_, az.id) }
      case _ => Seq()
    }}
    Util.groupByFirst(allZoneInputs)
  }

  def getZoneOutputsToDeclare(): Seq[(String,Type)] = {
    val allZoneOutputTypes = ng.idToStmt flatMap { _ match {
      case az: ActivityZone => az.outputsToDeclare.toSeq
      case _ => Seq()
    }}
    allZoneOutputTypes
  }

  def getExternalZoneInputNames(): Seq[String] = {
    val allZoneInputs = (ng.idToStmt flatMap { _ match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}).toSet
    val allZoneOutputs = (ng.idToStmt flatMap { _ match {
      case az: ActivityZone => az.outputsToDeclare.keys
      case _ => Seq()
    }}).toSet ++ alreadyDeclared.toSet
    (allZoneInputs -- allZoneOutputs).toSeq
  }

  def getExternalZoneInputTypes(extIOtypes: Map[String, Type]): Seq[(String,Type)] = {
    getExternalZoneInputNames() map {
      name => (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
    }
  }
}

object MakeCondPart {
  def apply(ng: NamedGraph) = {
    new MakeCondPart(ng)
  }
}
