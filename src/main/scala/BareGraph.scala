package essent

import collection.mutable.ArrayBuffer

// Directed graph class to be used as base for others
//  - uses numeric vertex identifiers (NodeID  which is type alias for Int)
//  - tracks edges both in outgoing and incomming directions

class BareGraph {
  // Access companion object's type aliases without prefix
  import BareGraph.{NodeID, AdjacencyList}
  
  // Internal data structures
  //----------------------------------------------------------------------------
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh: AdjacencyList = ArrayBuffer[ArrayBuffer[NodeID]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh: AdjacencyList = ArrayBuffer[ArrayBuffer[NodeID]]()


  // Graph building
  //----------------------------------------------------------------------------
  def addEdge(sourceID: NodeID, destID: NodeID) {
    def growNeighsIfNeeded(id: NodeID, neighs: AdjacencyList) {
      assert(id >= 0)
      if (id >= neighs.size) {
        val numElemsToGrow = id - neighs.size + 1
        neighs.appendAll(ArrayBuffer.fill(numElemsToGrow)(ArrayBuffer[NodeID]()))
      }
    }
    val maxID = math.max(sourceID, destID)
    growNeighsIfNeeded(maxID, outNeigh)
    growNeighsIfNeeded(maxID, inNeigh)
    outNeigh(sourceID) += destID
    inNeigh(destID) += sourceID
  }

  def addEdgeIfNew(sourceID: NodeID, destID: NodeID) {
    if ((sourceID >= outNeigh.size) || !outNeigh(sourceID).contains(destID))
      addEdge(sourceID, destID)
  }


  // Accessors
  //----------------------------------------------------------------------------
  def nodeRange() = 0 until outNeigh.size


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


  // Mutators
  //----------------------------------------------------------------------------
  def removeDuplicateEdges() {
    // will not remove self-loops
    def uniquifyNeighs(neighs: AdjacencyList) {
      (0 until neighs.size) foreach { id => neighs(id) = neighs(id).distinct }
    }
    uniquifyNeighs(outNeigh)
    uniquifyNeighs(inNeigh)
  }

  def mergeNodesMutably(mergeDest: NodeID, mergeSources: Seq[NodeID]) {
    val mergedID = mergeDest
    val idsToRemove = mergeSources
    def mergeNodeOneDirection(neighA: AdjacencyList, neighB: AdjacencyList) {
      val combinedDirNeigh = idsToRemove.flatMap(neighA(_)).distinct diff idsToRemove
      combinedDirNeigh foreach { id => {
        neighB(id) --= idsToRemove
        // TODO: reduce redundancy with AddEdgeIfNew
        if (!neighB(id).contains(mergedID)) neighB(id) += mergedID
      }}
      neighA(mergedID) = combinedDirNeigh.to[ArrayBuffer]
      idsToRemove foreach { deleteID => neighA(deleteID).clear() }
    }
    mergeNodeOneDirection(inNeigh, outNeigh)
    mergeNodeOneDirection(outNeigh, inNeigh)
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

object BareGraph {
  type NodeID = Int
  type AdjacencyList = ArrayBuffer[ArrayBuffer[NodeID]]
}
