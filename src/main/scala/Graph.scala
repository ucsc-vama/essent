package essent

import essent.Graph.NodeList

import collection.mutable.ArrayBuffer
import scala.xml.{Elem, NodeSeq}

// Directed graph class to be used as base for others
//  - uses numeric vertex identifiers (NodeID  which is type alias for Int)
//  - tracks edges both in outgoing and incomming directions

class Graph extends Serializable {
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

  /**
   * Similar to [[extPathExists]] except this returns all the reachable verticies from
   * the one source
   * @param f1 Function to apply to the initial frontier (use case: ensure it goes outside the GCSM)
   * @return subset (or empty) of the destSet, which are reachable from the source
   */
  def findExtPaths(source: NodeID, destSet: Set[NodeID], excludeSet: Set[NodeID]): Set[NodeID] = {
    val sourcesOnFringe = Set(source) filter {
      id => outNeigh(id) exists { neigh => source != neigh }
    }
    val startingExtFrontier = sourcesOnFringe flatMap outNeigh diff destSet
    def traverseUntilIntersect(frontier: Set[NodeID], reached: Set[NodeID]): Set[NodeID] = {
      if (frontier.isEmpty) Set.empty
      else {
        val nextFrontier = frontier flatMap outNeigh diff (reached ++ excludeSet)
        // find all reachable verts
        val foundPaths = (nextFrontier & destSet)
        foundPaths ++ traverseUntilIntersect(nextFrontier, reached ++ nextFrontier)
      }
    }
    traverseUntilIntersect(startingExtFrontier, Set(source) ++ startingExtFrontier ++ excludeSet)
  }

  def findExtPathsWithHistory(source: NodeID, destSet: Set[NodeID], excludeSet: Set[NodeID]): collection.Set[Seq[NodeID]] = {
    val sourcesOnFringe = Set(source) filter {
      id => outNeigh(id) exists { neigh => source != neigh }
    }
    val startingExtFrontier = sourcesOnFringe flatMap outNeigh diff destSet

    val backPairs = collection.mutable.Map[NodeID, NodeID]() // dest -> src
    def traverseUntilIntersect(frontier: collection.Set[NodeID], reached: Set[NodeID]): collection.Set[NodeID] = {
      if (frontier.isEmpty) Set.empty
      else {
        //val nextFrontier = frontier flatMap outNeigh diff (reached ++ excludeSet)
        val nextFrontier = collection.mutable.Set[NodeID]()
        val nope = reached ++ excludeSet
        frontier foreach { id =>
          val outNeighs = outNeigh(id).toSet -- nope
          nextFrontier ++= outNeighs
          outNeighs foreach { outID => backPairs(outID) = id }
        }
        // find all reachable verts
        (nextFrontier & destSet) ++ traverseUntilIntersect(nextFrontier, reached ++ nextFrontier)
      }
    }
    val reachableDests = traverseUntilIntersect(startingExtFrontier, Set(source) ++ startingExtFrontier ++ excludeSet)

    def walkBackwards(dest: NodeID): Seq[NodeID] = {
      if (dest == source) Seq(source)
      else if (startingExtFrontier.contains(dest)) Seq(dest, source)
      else {
        val nextDest = backPairs(dest)
        Seq(dest) ++ walkBackwards(nextDest)
      }
    }
    reachableDests.map(id => walkBackwards(id).reverse)
  }

  def mergeIsAcyclic(u: NodeID, v: NodeID): Boolean = !extPathExists(u,v) && !extPathExists(v,u)

  // TODO: speed up by doing a single traversal
//  def mergeIsAcyclic(ids: Set[NodeID]): Boolean = {
//    ids forall { source => !extPathExists(Set(source), ids - source) }
//  }
  def mergeIsAcyclic(ids: Set[NodeID]): Boolean = {
    ids forall { source =>
      val thePath = findExtPathsWithHistory(source, ids - source, Set.empty)
      val tmp = !extPathExists(Set(source), ids - source)
      assert(tmp == thePath.isEmpty, "disagreement over if there's a path")
      thePath.isEmpty
    }
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

  /**
   * Save the graph in GEXF format (for loading in e.g. Gephi)
   *
   * Caution: very slow and memory-hungry
   * @param destFile output filename
   * @param labelFunc called for each node, if defined there then it adds a label attribute
   */
  def saveAsGEXF(destFile: String, labelFunc: PartialFunction[NodeID, String]): Unit = {
    val notDefinedFunc: PartialFunction[NodeID, NodeSeq] = { case _ => NodeSeq.Empty }
    val labelFunc2 = labelFunc
      .andThen(label => <attvalue for="0" value={label} />)
      .orElse(notDefinedFunc)
    val nodes = nodeRange().map({ id =>
      Seq(
        <node id={id.toString}>
          <attvalues>
            {labelFunc2(id)}
            <attvalue for="1" value={idToTag(id).toString}/>
          </attvalues>
        </node>,
        outNeigh(id).toStream.map(destID =>
            <edge id={s"$id-$destID"} source={id.toString} target={destID.toString}/>
        )
      )
    }).transpose

    val gexf = <gexf xmlns="http://www.gexf.net/1.2draft" version="1.2">
      <meta>
        <creator>ESSENT</creator>
      </meta>
      <graph mode="static" defaultedgetype="directed">
        <attributes class="node">
          <attribute id="0" title="serialized" type="string" />
          <attribute id="1" title="tag" type="string" />
        </attributes>
        <nodes>
          {nodes.head}
        </nodes>
        <edges>
          {nodes.tail}
        </edges>
      </graph>
    </gexf>

    scala.xml.XML.save(destFile, gexf)
  }

  def saveAsGEXF(destFile: String): Unit = saveAsGEXF(destFile, PartialFunction.empty)
}

object Graph {
  type NodeID = Int
  type NodeList = ArrayBuffer[NodeID]
  type AdjacencyList = ArrayBuffer[NodeList]
}
