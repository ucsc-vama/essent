package essent

import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// Fundamental assumptions:
//  * IDs match up with IDs in original BareGraph
//  * The mergeID is a member of the merged group and ID used

class MergeGraph extends BareGraph {
  // node ID -> merge ID
  val idToMergeID = ArrayBuffer[Int]()

  // merge ID -> [member] node IDs (must include mergeID)
  val mergeIDToMembers = HashMap[Int, Seq[Int]]()

  // inherits outNeigh and inNeigh from BareGraph

  def buildFromInitialAssignments(initialAssignments: ArrayBuffer[Int]) {
    // FUTURE: support negative (unassigned) initial assignments
    initialAssignments.copyToBuffer(idToMergeID)
    val asMap = Util.groupIndicesByValue(initialAssignments)
    asMap foreach { case (mergeID, members) => {
      assert(members.contains(mergeID))
      mergeIDToMembers(mergeID) = members
      mergeNodesMutably(mergeID, members diff Seq(mergeID))
    }}
  }
}


object MergeGraph {
  def apply(og: BareGraph, initialAssignments: ArrayBuffer[Int]) = {
    // FUTURE: cleaner way to do this with clone on superclass?
    val mg = new MergeGraph
    og.outNeigh.copyToBuffer(mg.outNeigh)
    og.inNeigh.copyToBuffer(mg.inNeigh)
    mg.buildFromInitialAssignments(initialAssignments)
    mg
  }
}
