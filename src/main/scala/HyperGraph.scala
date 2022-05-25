package essent

import collection.mutable.ArrayBuffer
import collection.mutable.HashMap

// Weighted hyper graph class
// - Uses bi-partite representation
// - Assuming node ids are continues Int starts from 0
class HyperGraph {

  val nodes = ArrayBuffer[ArrayBuffer[Int]]()
  val edges = ArrayBuffer[ArrayBuffer[Int]]()

  val nodeWeight = ArrayBuffer[Int]()
  val edgeWeight = ArrayBuffer[Int]()


  def addNode(id: Int, weight: Int): Unit = {
    if (id >= nodes.size) {
      val numElemsToGrow = id - nodes.size + 1
      nodes.appendAll(ArrayBuffer.fill(numElemsToGrow)(ArrayBuffer[Int]()))
      nodeWeight.appendAll(ArrayBuffer.fill(numElemsToGrow)(-1))
    }

    nodeWeight(id) = weight
  }

  def addEdge(edge: ArrayBuffer[Int], weight: Int): Unit = {
    assert(edge.nonEmpty)
    val edge_id = edges.length

    edges += edge
    edgeWeight += weight

    edge.foreach {nid => {
      nodes(nid) += edge_id
    }}
  }

}

object HyperGraph {

}