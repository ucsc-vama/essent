package essent

import essent.BareGraph.NodeID
import essent.Extract._
import essent.ir._

import firrtl.ir._

import collection.mutable.BitSet


object MakeCondMux {
  // embed inside apply?
  def crawlBack(ng: NamedGraph, sources: Seq[NodeID], dontPass: BitSet, muxID: NodeID) = {
    val q = new scala.collection.mutable.Queue[NodeID]
    val reached = BitSet() ++ Seq(muxID)
    def allChildrenReached(u: NodeID) = ng.outNeigh(u) forall reached
    val initialFrontier = sources filter (v => !dontPass(v) && allChildrenReached(v))
    reached ++= initialFrontier
    q ++= initialFrontier flatMap ng.inNeigh
    while (q.nonEmpty) {
      val v = q.dequeue
      if (!dontPass(v) && !reached(v) & allChildrenReached(v)) {
        reached += v
        q ++= ng.inNeigh(v)
      }
    }
    (reached - muxID).toSeq
  }

  // TODO: pull into generalized MFFC finder
  // TODO: figure out how to make faster
  def findMaxSafeWay(ng: NamedGraph, sources: Seq[NodeID], dontPass: Set[NodeID], muxID: NodeID) = {
    def crawlBackToFindMFFC(frontier: Set[NodeID], inMFFC: Set[NodeID]): Set[NodeID] = {
      def allChildrenIncluded(u: NodeID) = ng.outNeigh(u) forall inMFFC
      if (frontier.nonEmpty) {
        val toInclude = frontier filter {
          v => !dontPass(v) && !inMFFC(v) & allChildrenIncluded(v)
        }
        val nextFrontier = frontier flatMap ng.inNeigh
        val expandedMFFC = inMFFC ++ toInclude
        crawlBackToFindMFFC(nextFrontier, expandedMFFC)
      } else inMFFC
    }
    (crawlBackToFindMFFC(sources.toSet, Set(muxID)) - muxID).toSeq
  }

  // FUTURE: consider creating all MuxShadowed statements on first pass (including nested)
  // FUTURE: pull mux chains into if else chains to reduce indent depth
  // FUTURE: consider mux size threshold
  def apply(ng: NamedGraph) {
    val muxIDs = ng.idToStmt.zipWithIndex collect {
      case (DefNode(_, _, m: Mux), id) => id
      case (Connect(_, _, m: Mux), id) => id
    }
    val muxIDToWays = (muxIDs map { muxID => {
      val muxExpr = grabMux(ng.idToStmt(muxID))
      val traversalLimits = BitSet() ++ ng.extractSourceIDs(muxExpr.cond)
      val tWay = crawlBack(ng, ng.extractSourceIDs(muxExpr.tval), traversalLimits ++ ng.extractSourceIDs(muxExpr.fval), muxID)
      val fWay = crawlBack(ng, ng.extractSourceIDs(muxExpr.fval), traversalLimits ++ ng.extractSourceIDs(muxExpr.tval), muxID)
      (muxID -> (tWay, fWay))
    }}).toMap
    val muxIDSet = muxIDs.toSet
    val nestedMuxes = muxIDToWays flatMap {
      case (muxID, (tWay, fWay)) => (tWay ++ fWay) filter muxIDSet
    }
    val topLevelMuxes = muxIDSet -- nestedMuxes
    val muxesWorthShadowing = topLevelMuxes filter { muxID => {
      val (tWay, fWay) = muxIDToWays(muxID)
      // tWay.nonEmpty || fWay.nonEmpty
    }}
    // just make defnode at end for ways instead of replacing?
    def replaceMux(newResult: Expression)(e: Expression): Expression = e match {
      case m: Mux => newResult
      case _ => e
    }
    muxesWorthShadowing foreach { muxID => {
      val muxExpr = grabMux(ng.idToStmt(muxID))
      val muxStmtName = ng.idToName(muxID)
      val (tWay, fWay) = muxIDToWays(muxID)
      val cmStmt = CondMux(muxStmtName, muxExpr,
                     ng.collectValidStmts(tWay) :+ (ng.idToStmt(muxID) mapExpr replaceMux(muxExpr.tval)),
                     ng.collectValidStmts(fWay) :+ (ng.idToStmt(muxID) mapExpr replaceMux(muxExpr.fval)))
      ng.mergeStmtsMutably(muxID, tWay ++ fWay, cmStmt)
    }}
  }
}