package essent

import essent.Graph.NodeID
import essent.Emitter._
import essent.ir._
import firrtl._
import firrtl.ir._
import firrtl.transforms.DedupedResult
import logger.LazyLogging

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer



object DedupWorker {

  // Find nodes in [instTarget] instance that corresponding to nodes in [instTemplate] instance
  // Assumes nodes in [templateNodes] are all nodes in instance [instTarget]
  def alignInstance(instTemplate: String, templateNodes: Seq[NodeID], instTarget: String, sg: StatementGraph) = {
    val alignTable = templateNodes.map{nid => {
      val canonicalName = sg.idToName(nid)
      val normalizedName = canonicalName.stripPrefix(instTemplate)
      val targetName = instTarget + normalizedName
      val targetNodeId = sg.nameToID(targetName)
      nid -> targetNodeId
    }}.toMap

    alignTable
  }


}
