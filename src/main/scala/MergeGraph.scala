package essent

import Graph.NodeID
import essent.Util.IterableUtils

import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// Fundamental assumptions:
//  * IDs match up with IDs in original Graph
//  * The mergeID is a member of the merged group and ID used
//  * MergeGraph will not add new nodes after built

class MergeGraph extends Graph with Serializable {
  // node ID -> merge ID
  val idToMergeID = ArrayBuffer[NodeID]()

  // merge ID -> [member] node IDs (must include mergeID)
  val mergeIDToMembers = HashMap[NodeID, Seq[NodeID]]()

  // inherits outNeigh and inNeigh from Graph

  def buildFromGraph(g: Graph) {
    // FUTURE: cleaner way to do this with clone on superclass?
    outNeigh.appendAll(ArrayBuffer.fill(g.numNodes)(ArrayBuffer[NodeID]()))
    inNeigh.appendAll(ArrayBuffer.fill(g.numNodes)(ArrayBuffer[NodeID]()))
    idToTag.appendAll(g.idToTag)
    g.nodeRange foreach { id => {
      g.outNeigh(id).copyToBuffer(outNeigh(id))
      g.inNeigh(id).copyToBuffer(inNeigh(id))
    }}
    nodeRange().copyToBuffer(idToMergeID)
    nodeRange() foreach { id  => mergeIDToMembers(id) = Seq(id) }
  }

  /**
   * Apply a given sequence of initial merges.
   * @note This clears any existing merges!
   * @param initialAssignments list of merges. the value at any given index determines what other index (or itself) to merge into
   */
  def applyInitialAssignments(initialAssignments: Iterable[NodeID]) {
    // FUTURE: support negative (unassigned) initial assignments
    idToMergeID.clear()
    mergeIDToMembers.clear()
    initialAssignments.copyToBuffer(idToMergeID)
    val asMap = Util.groupIndicesByValue(initialAssignments)
    asMap foreach { case (mergeID, members) => {
      assert(members.contains(mergeID))
      mergeIDToMembers(mergeID) = members
      mergeNodesMutably(mergeID, members diff Seq(mergeID))
    }}
  }

  def mergeGroups(mergeDest: NodeID, mergeSources: Seq[NodeID]) {
    val newMembers = mergeSources flatMap mergeIDToMembers
    newMembers foreach { id => idToMergeID(id) = mergeDest}
    mergeIDToMembers(mergeDest) ++= newMembers
    mergeSources foreach { id => mergeIDToMembers.remove(id) }
    mergeNodesMutably(mergeDest, mergeSources)
  }

  def nodeSize(n: NodeID) = mergeIDToMembers.getOrElse(n,Seq()).size

  def iterGroups() = mergeIDToMembers

  def groupsByTag() = iterGroups().toStream.collect({
    case (clusterID, nodes) => idToTag(clusterID) -> (clusterID -> nodes)
  }).toMapOfLists
}


object MergeGraph {
  def apply(g: Graph): MergeGraph = {
    val mg = new MergeGraph
    mg.buildFromGraph(g)
    mg
  }

  def apply(g: Graph, initialAssignments: ArrayBuffer[NodeID]): MergeGraph = {
    // TODO: remove unecessary building if using initialAssignments
    val mg = apply(g)
    mg.applyInitialAssignments(initialAssignments)
    mg
  }
}
