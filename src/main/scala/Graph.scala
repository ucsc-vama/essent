package essent

import essent.Graph.NodeList

import collection.mutable.ArrayBuffer

// Directed graph class to be used as base for others
//  - uses numeric vertex identifiers (NodeID  which is type alias for Int)
//  - tracks edges both in outgoing and incomming directions

class Graph {
  // Access companion object's type aliases without prefix
  import Graph.{NodeID, AdjacencyList}
  
  // Internal data structures
  //----------------------------------------------------------------------------
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh: AdjacencyList = ArrayBuffer[ArrayBuffer[NodeID]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh: AdjacencyList = ArrayBuffer[ArrayBuffer[NodeID]]()
  // Numeric vertex ID -> module instance name (tag)
  val idToTag: ArrayBuffer[String] = ArrayBuffer[String]()

  // Graph building
  //----------------------------------------------------------------------------
  def growNeighsIfNeeded(id: NodeID) {
    assert(id >= 0)
    if (id >= outNeigh.size) {
      val numElemsToGrow = id - outNeigh.size + 1
      outNeigh.appendAll(ArrayBuffer.fill(numElemsToGrow)(ArrayBuffer[NodeID]()))
      inNeigh.appendAll(ArrayBuffer.fill(numElemsToGrow)(ArrayBuffer[NodeID]()))
      idToTag.appendAll(ArrayBuffer.fill(numElemsToGrow)(""))
    }
  }

  def addEdge(sourceID: NodeID, destID: NodeID) {
    growNeighsIfNeeded(math.max(sourceID, destID))
    outNeigh(sourceID) += destID
    inNeigh(destID) += sourceID
  }

  def addEdgeIfNew(sourceID: NodeID, destID: NodeID) {
    if ((sourceID >= outNeigh.size) || !outNeigh(sourceID).contains(destID))
      addEdge(sourceID, destID)
  }


  // Accessors
  //----------------------------------------------------------------------------
  def nodeRange() = outNeigh.indices

  /**
   * Get an iterator to iterate over each node, and information about it.
   * @return iterable of (NodeID, inNeighs, outNeighs, tag)
   */
  def iterNodes = new Iterator[(NodeID, NodeList, NodeList, String)]() {
    private val ids = nodeRange().toIterator
    private val inNeighs = inNeigh.toIterator
    private val outNeighs = outNeigh.toIterator
    private val tags = idToTag.toIterator
    override def hasNext: Boolean = ids.hasNext && inNeighs.hasNext && outNeighs.hasNext && tags.hasNext
    override def next(): (NodeID, NodeList, NodeList, String) = (ids.next(), inNeighs.next(), outNeighs.next(), tags.next())
  }.toIterable


  // Traversals / Queries
  //----------------------------------------------------------------------------
  // TODO: make NodeSet type?
  // TODO: speed advantages of using BitSet in places?
  // TODO: speed advantages of using less Set-like structures?
  def extPathExists(source: NodeID, dest: NodeID): Boolean = extPathExists(Set(source), Set(dest))

  def extPathExists(sourceSet: Set[NodeID], destSet: Set[NodeID]): Boolean = {
    val sourcesOnFringe = sourceSet filter {
      id => outNeigh(id) exists { neigh => !sourceSet.contains(neigh) }
    }
    val startingExtFrontier = sourcesOnFringe flatMap outNeigh diff destSet
    def traverseUntilIntersect(frontier: Set[NodeID], reached: Set[NodeID]): Boolean = {
      if (frontier.isEmpty) false
      else {
        val nextFrontier = frontier flatMap outNeigh diff reached
        if ((nextFrontier & destSet).nonEmpty) true
        else traverseUntilIntersect(nextFrontier, reached ++ nextFrontier)
      }
    }
    traverseUntilIntersect(startingExtFrontier, sourceSet ++ startingExtFrontier)
  }

  def mergeIsAcyclic(u: NodeID, v: NodeID): Boolean = !extPathExists(u,v) && !extPathExists(v,u)

  // TODO: speed up by doing a single traversal
  def mergeIsAcyclic(ids: Set[NodeID]): Boolean = {
    ids forall { source => !extPathExists(Set(source), ids - source) }
  }

  /**
   * Find the longest path to the root from the given node
   * @param id the node ID to query
   * @return number of steps to the root for the given node ID
   */
  def nodeDepth(id: NodeID): Int = {
    if (inNeigh(id).isEmpty) 0 // this is the root
    else {
      // for each in neighbor, find the distance to the root
      inNeigh(id).minBy(1 + nodeDepth(_))
    }
  }

  /**
   * Check if we can merge two nodes on the basis of their tag values
   */
  def mergeIsTagSame(u: NodeID, v: NodeID): Boolean = idToTag(u) == idToTag(v)
  def mergeIsTagSame(ids: Set[NodeID]): Boolean = {
    val first = idToTag(ids.head)
    ids.tail forall { idToTag(_) == first }
  }

  // Mutators
  //----------------------------------------------------------------------------
  def removeDuplicateEdges() {
    // will not remove self-loops
    def uniquifyNeighs(neighs: AdjacencyList) {
      neighs.indices foreach { id => neighs(id) = neighs(id).distinct }
    }
    uniquifyNeighs(outNeigh)
    uniquifyNeighs(inNeigh)
  }

  def mergeNodesMutably(mergeDest: NodeID, mergeSources: Seq[NodeID]) {
    val mergedID = mergeDest
    val idsToRemove = mergeSources
    val idsToMerge = mergeSources :+ mergeDest
    val combinedInNeigh = idsToMerge.flatMap(inNeigh).distinct diff idsToMerge
    val combinedOutNeigh = idsToMerge.flatMap(outNeigh).distinct diff idsToMerge
    // TODO: reduce redundancy with AddEdgeIfNew
    combinedInNeigh foreach { inNeighID => {
      outNeigh(inNeighID) --= idsToRemove
      if (!outNeigh(inNeighID).contains(mergedID)) outNeigh(inNeighID) += mergedID
    }}
    combinedOutNeigh foreach { outNeighID => {
      inNeigh(outNeighID) --= idsToRemove
      if (!inNeigh(outNeighID).contains(mergedID)) inNeigh(outNeighID) += mergedID
    }}
    inNeigh(mergedID) = combinedInNeigh.to[ArrayBuffer]
    outNeigh(mergedID) = combinedOutNeigh.to[ArrayBuffer]
    idsToRemove foreach { deleteID => {
      inNeigh(deleteID).clear()
      outNeigh(deleteID).clear()
    }}
  }


  // Stats
  //----------------------------------------------------------------------------
  // assumes outNeigh and inNeigh grow together (they should)
  def numNodes() = outNeigh.size

  def computeDegrees(neighs: AdjacencyList) = {
    neighs map { _.size }
  }

  def numEdges() = computeDegrees(outNeigh).sum
}

object Graph {
  type NodeID = Int
  type NodeList = ArrayBuffer[NodeID]
  type AdjacencyList = ArrayBuffer[NodeList]
}
