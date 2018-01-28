package essent

import firrtl._
import firrtl.ir._

import essent.Emitter._
import essent.Extract._
import essent.ir._

import collection.mutable.{ArrayBuffer, BitSet}

class StatementGraph extends Graph {
  // Vertex ID -> firrtl statement (Block used for aggregates)
  val idToStmt = ArrayBuffer[Statement]()

  // make sure idToStmt is as big as needed and tracks id of internal graph
  override def getID(vertexName: String) = {
    val id = super.getID(vertexName)
    while (id >= idToStmt.size)
      idToStmt += EmptyStmt
    id
  }

  def buildFromBodies(bodies: Seq[Statement]) {
    val bodyHE = bodies flatMap {
      case b: Block => b.stmts flatMap findDependencesStmt
      case s => findDependencesStmt(s)
    }
    bodyHE foreach { he => {
      addNodeWithDeps(he.name, he.deps)
      idToStmt(getID(he.name)) = he.stmt
    }}
  }

  def stmtsOrdered(): Seq[Statement] = {
    topologicalSort filter validNodes map idToStmt
  }

  def updateMergedRegWrites(mergedRegs: Seq[String]) {
    mergedRegs foreach { regName => {
      val regWriteName = regName + "$next"
      val regWriteID = nameToID(regWriteName)
      val newName = s"if (update_registers) $regName"
      idToStmt(regWriteID) = replaceNamesStmt(Map(regWriteName -> newName))(idToStmt(regWriteID))
    }}
  }

  def findMuxIDs(): Seq[Int] = idToStmt.zipWithIndex flatMap {
    case (stmt, id) => { stmt match {
      case DefNode(_, _, Mux(_, _, _, _)) => Seq(id)
      case Connect(_, _, Mux(_, _, _, _)) => Seq(id)
      case _ => Seq()
    }}
  }

  // FUTURE: consider creating all MuxShadowed statements on first pass (including nested)
  def coarsenMuxShadows(dontPassSigs: Seq[String]) {
    val muxIDs = findMuxIDs
    val dontPass = BitSet() ++ dontPassSigs.filter(nameToID.contains).map(nameToID)
    def convToStmts(ids: Seq[Int]): Seq[Statement] = ids map idToStmt
    val muxIDToShadows = (muxIDs map { muxID => {
      val muxExpr = grabMux(idToStmt(muxID))
      val tShadow = crawlBack(grabIDs(muxExpr.tval), dontPass, muxID) map nameToID
      val fShadow = crawlBack(grabIDs(muxExpr.fval), dontPass, muxID) map nameToID
      (muxID -> (tShadow, fShadow))
    }}).toMap
    val muxIDSet = muxIDs.toSet
    val nestedMuxes = muxIDToShadows flatMap {
      case (muxID, (tShadow, fShadow)) => (tShadow ++ fShadow) filter muxIDSet
    }
    val topLevelMuxes = muxIDSet -- nestedMuxes
    topLevelMuxes foreach { muxID => {
      val muxExpr = grabMux(idToStmt(muxID))
      val muxOutputName = idToName(muxID)
      val (tShadow, fShadow) = muxIDToShadows(muxID)
      idToStmt(muxID) = MuxShadowed(muxOutputName, muxExpr, convToStmts(tShadow), convToStmts(fShadow))
      val idsToRemove = tShadow ++ fShadow
      idsToRemove foreach { id => idToStmt(id) = EmptyStmt }
      val namesOfShadowMembers = (tShadow ++ fShadow) map idToName
      super.mergeNodesMutably(Seq(muxOutputName) ++ namesOfShadowMembers)
    }}
  }
}


object StatementGraph {
  def apply(bodies: Seq[Statement]) = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg
  }
}