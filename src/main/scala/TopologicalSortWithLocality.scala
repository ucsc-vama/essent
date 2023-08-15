package essent

import essent.Graph.NodeID

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object TopologicalSortWithLocality {

  def apply(inputGraph: Graph, localityRequests: Seq[Seq[NodeID]]): ArrayBuffer[NodeID] = {
    val g = Graph(inputGraph)
    val merges = mutable.HashMap[NodeID, ArrayBuffer[NodeID]]()

    // Try merge all dedup parts
    localityRequests.foreach{group => {
      val groupHead = group.head
      group.tail.foreach{mid => {
        if (g.mergeIsAcyclic(groupHead, mid)) {
          if (!merges.contains(groupHead)) {
            merges(groupHead) = ArrayBuffer[NodeID](groupHead)
          }
          merges(groupHead) += mid
          g.mergeNodesMutably(groupHead, Seq(mid))
        }
      }}
    }}

    val sorted = TopologicalSort(g)

    sorted.flatMap(id => merges.getOrElse(id, Seq(id)))
  }
}
