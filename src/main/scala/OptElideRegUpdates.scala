package essent

import essent.Graph.NodeID
import essent.ir._

import logger._
import firrtl.ir._


object OptElideRegUpdates extends LazyLogging {
  def apply(sg: StatementGraph) {
    def safeToMergeWithParentNextNode(u: NodeID): Boolean = {
      sg.inNeigh(u).nonEmpty &&                              // node u isn't floating (parentless)
      sg.idToName(sg.inNeigh(u).head).endsWith("$next") &&   // first parent assigns $next
      sg.mergeIsAcyclic(u, sg.inNeigh(u).head)               // no external paths between them
    }
    val regUpdateIDs = sg.findIDsOfStmtOfType[RegUpdate]()
    // WARNING: following filter will have side-effects on NamedGraph ng
    val elidedRegIDs = regUpdateIDs collect { case id if (safeToMergeWithParentNextNode(id)) => {
      val nextID = sg.inNeigh(id).head
      val nextExpr = sg.idToStmt(nextID) match {
        case c: Connect => c.expr
        case dn: DefNode => dn.value
        case _ => throw new Exception("$next statement is not a Connect or DefNode")
      }
      val finalRegUpdate = sg.idToStmt(id) match {
        case ru: RegUpdate => ru
        case _ => throw new Exception("$final statement is not a RegUpdate")
      }
      sg.mergeStmtsMutably(id, Seq(nextID), finalRegUpdate.copy(expr = nextExpr))
    }}
    logger.info(s"Was able to elide ${elidedRegIDs.size}/${regUpdateIDs.size} intermediate reg updates")
  }
}
