package essent

import Graph.NodeID

import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// Fundamental assumptions:
//  * IDs match up with IDs in original Graph
//  * The mergeID is a member of the merged group and ID used
//  * MergeGraph will not add new nodes after built

class MergeGraph extends Graph {
  // node ID -> merge ID
  val idToMergeID = ArrayBuffer[NodeID]()

  // merge ID -> [member] node IDs (must include mergeID)
  val mergeIDToMembers = HashMap[NodeID, Seq[NodeID]]()

  // inherits outNeigh and inNeigh from Graph

  def buildFromGraph(g: Graph): Unit = {
    // FUTURE: cleaner way to do this with clone on superclass?
    outNeigh.appendAll(ArrayBuffer.fill(g.numNodes())(ArrayBuffer[NodeID]()))
    inNeigh.appendAll(ArrayBuffer.fill(g.numNodes())(ArrayBuffer[NodeID]()))
    g.nodeRange() foreach { id => {
      outNeigh(id) ++= g.outNeigh(id)
      inNeigh(id) ++= g.inNeigh(id)
    }}
    idToMergeID ++= ArrayBuffer.range(0, numNodes())
    nodeRange() foreach { id  => mergeIDToMembers(id) = Seq(id) }
  }

  def applyInitialAssignments(initialAssignments: ArrayBuffer[NodeID]): Unit = {
    // FUTURE: support negative (unassigned) initial assignments
    idToMergeID.clear()
    mergeIDToMembers.clear()
    idToMergeID ++= initialAssignments
    val asMap = Util.groupIndicesByValue(initialAssignments)
    asMap foreach { case (mergeID, members) => {
      assert(members.contains(mergeID))
      mergeIDToMembers(mergeID) = members
      mergeNodesMutably(mergeID, members diff Seq(mergeID))
    }}
  }

  def mergeGroups(mergeDest: NodeID, mergeSources: Seq[NodeID]): Unit = {
    val newMembers = mergeSources flatMap mergeIDToMembers
    newMembers foreach { id => idToMergeID(id) = mergeDest}
    mergeIDToMembers(mergeDest) ++= newMembers
    mergeSources foreach { id => mergeIDToMembers.remove(id) }
    mergeNodesMutably(mergeDest, mergeSources)
  }

  def nodeSize(n: NodeID) = mergeIDToMembers.getOrElse(n,Seq()).size

  def iterGroups() = mergeIDToMembers
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
