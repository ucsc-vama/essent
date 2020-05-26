package essent

// TODO: remove this Extract import which is the only way to get logging to work
import essent.Extract._
import essent.BareGraph.NodeID
import essent.ir._

import firrtl.ir._


object OptElideRegUpdates {
  def apply(ng: NamedGraph) {
    def safeToMergeWithParentNextNode(u: NodeID): Boolean = {
      ng.inNeigh(u).nonEmpty &&                              // node u isn't floating (parentless)
      ng.idToName(ng.inNeigh(u).head).endsWith("$next") &&   // first parent assigns $next
      ng.mergeIsAcyclic(u, ng.inNeigh(u).head)               // no external paths between them
    }
    val regUpdateIDs = ng.findIDsOfStmtOfType[RegUpdate]()
    // WARNING: following filter will have side-effects on NamedGraph ng
    val elidedRegIDs = regUpdateIDs collect { case id if (safeToMergeWithParentNextNode(id)) => {
      val nextID = ng.inNeigh(id).head
      val nextExpr = ng.idToStmt(nextID) match {
        case c: Connect => c.expr
        case dn: DefNode => dn.value
        case _ => throw new Exception("$next statement is not a Connect or DefNode")
      }
      val finalRegUpdate = ng.idToStmt(id) match {
        case ru: RegUpdate => ru
        case _ => throw new Exception("$final statement is not a RegUpdate")
      }
      ng.mergeStmtsMutably(id, Seq(nextID), finalRegUpdate.copy(expr = nextExpr))
    }}
    logger.info(s"Was able to elide ${elidedRegIDs.size}/${regUpdateIDs.size} intermediate reg updates")
  }
}
