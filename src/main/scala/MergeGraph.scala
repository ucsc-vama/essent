package essent

import BareGraph.NodeID

import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// Fundamental assumptions:
//  * IDs match up with IDs in original BareGraph
//  * The mergeID is a member of the merged group and ID used
//  * MergeGraph will not add new nodes after built

class MergeGraph extends BareGraph {
  // node ID -> merge ID
  val idToMergeID = ArrayBuffer[NodeID]()

  // merge ID -> [member] node IDs (must include mergeID)
  val mergeIDToMembers = HashMap[NodeID, Seq[NodeID]]()

  // inherits outNeigh and inNeigh from BareGraph

  def buildFromBareGraph(og: BareGraph) {
    // FUTURE: cleaner way to do this with clone on superclass?
    outNeigh.appendAll(ArrayBuffer.fill(og.numNodes)(ArrayBuffer[NodeID]()))
    inNeigh.appendAll(ArrayBuffer.fill(og.numNodes)(ArrayBuffer[NodeID]()))
    og.nodeRange foreach { id => {
      og.outNeigh(id).copyToBuffer(outNeigh(id))
      og.inNeigh(id).copyToBuffer(inNeigh(id))
    }}
    ArrayBuffer.range(0, numNodes()).copyToBuffer(idToMergeID)
    nodeRange() foreach { id  => mergeIDToMembers(id) = Seq(id) }
  }

  def applyInitialAssignments(initialAssignments: ArrayBuffer[NodeID]) {
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
    val newMembers = (mergeSources map mergeIDToMembers).flatten
    newMembers foreach { id => idToMergeID(id) = mergeDest}
    mergeIDToMembers(mergeDest) ++= newMembers
    mergeSources foreach { id => mergeIDToMembers.remove(id) }
    mergeNodesMutably(mergeDest, mergeSources)
  }

  def nodeSize(n: NodeID) = mergeIDToMembers.getOrElse(n,Seq()).size

  def iterGroups() = mergeIDToMembers
}


object MergeGraph {
  def apply(og: BareGraph): MergeGraph = {
    val mg = new MergeGraph
    mg.buildFromBareGraph(og)
    mg
  }

  def apply(og: BareGraph, initialAssignments: ArrayBuffer[NodeID]): MergeGraph = {
    // TODO: remove unecessary building if using initialAssignments
    val mg = apply(og)
    mg.applyInitialAssignments(initialAssignments)
    mg
  }
}
