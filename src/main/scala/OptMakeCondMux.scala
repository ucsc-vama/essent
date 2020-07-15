package essent

import essent.BareGraph.NodeID
import essent.Extract._
import essent.ir._

import firrtl.ir._


class MakeCondMux(val ng: NamedGraph, keepAvail: Set[NodeID]) {
  // TODO: pull into generalized MFFC finder
  def findMaxSafeWay(muxID: NodeID, muxCond: Expression, thisWay: Expression, otherWay: Expression) = {
    val dontPass = ng.extractSourceIDs(muxCond).toSet ++ ng.extractSourceIDs(otherWay) ++ keepAvail
    def crawlBackToFindMFFC(frontier: Set[NodeID], inMFFC: Set[NodeID]): Set[NodeID] = {
      def allChildrenIncluded(u: NodeID) = ng.outNeigh(u) forall inMFFC
      if (frontier.nonEmpty) {
        val toInclude = frontier filter {
          v => !dontPass(v) && !inMFFC(v) & allChildrenIncluded(v)
        }
        val nextFrontier = toInclude flatMap ng.inNeigh
        val expandedMFFC = inMFFC ++ toInclude
        crawlBackToFindMFFC(nextFrontier, expandedMFFC)
      } else inMFFC
    }
    val sources = ng.extractSourceIDs(thisWay).toSet
    (crawlBackToFindMFFC(sources, Set(muxID)) - muxID).toSeq
  }

  def makeMuxOutputStmt(muxID: NodeID, muxWay: Expression): Statement = {
    def replaceMux(newResult: Expression)(e: Expression): Expression = e match {
      case m: Mux => newResult
      case _ => e
    }
    ng.idToStmt(muxID) mapExpr replaceMux(muxWay)
  }

  def makeCondMuxesTopDown(muxIDsRemaining: Set[NodeID], muxIDToWays: Map[NodeID,(Seq[NodeID],Seq[NodeID])]) {
    val muxesWithMuxesInside = muxIDToWays collect {
      case (muxID, (tWay, fWay)) if ((tWay ++ fWay) exists muxIDsRemaining) => muxID
    }
    val baseMuxes = muxIDsRemaining -- muxesWithMuxesInside
    if (baseMuxes.nonEmpty) {
      // println(s"found ${muxIDsRemaining.size} muxes were big enough and ${baseMuxes.size} are base")
      baseMuxes foreach { muxID => {
        val muxExpr = grabMux(ng.idToStmt(muxID))
        val muxStmtName = ng.idToName(muxID)
        val (tWay, fWay) = muxIDToWays(muxID)
        val cmStmt = CondMux(muxStmtName, muxExpr,
                       ng.collectValidStmts(tWay) :+ makeMuxOutputStmt(muxID, muxExpr.tval),
                       ng.collectValidStmts(fWay) :+ makeMuxOutputStmt(muxID, muxExpr.fval))
        ng.mergeStmtsMutably(muxID, tWay ++ fWay, cmStmt)
      }}
      makeCondMuxesTopDown(muxesWithMuxesInside.toSet, muxIDToWays)
    }
  }

  def doOpt() {
    val muxIDs = (ng.idToStmt.zipWithIndex collect {
      case (DefNode(_, _, m: Mux), id) => id
      case (Connect(_, _, m: Mux), id) => id
    }).toSet
    val muxIDToWays = (muxIDs map { muxID => {
      val muxExpr = grabMux(ng.idToStmt(muxID))
      val traversalLimits = ng.extractSourceIDs(muxExpr.cond).toSet
      val tWay = findMaxSafeWay(muxID, muxExpr.cond, muxExpr.tval, muxExpr.fval)
      val fWay = findMaxSafeWay(muxID, muxExpr.cond, muxExpr.fval, muxExpr.tval)
      (muxID -> (tWay, fWay))
    }}).toMap
    val nonEmptyMuxes = muxIDs filter { muxID => {
      val (tWay, fWay) = muxIDToWays(muxID)
      (tWay.size + fWay.size) > 0
    }}
    makeCondMuxesTopDown(nonEmptyMuxes, muxIDToWays)
  }
}


object MakeCondMux {
  // FUTURE: pull mux chains into if else chains to reduce indent depth
  // FUTURE: consider mux size threshold
  def apply(ng: NamedGraph, keepAvailNames: Set[String] = Set()) {
    val keepAvailIDs = keepAvailNames map ng.nameToID
    val optimizer = new MakeCondMux(ng, keepAvailIDs)
    optimizer.doOpt()
  }
}
