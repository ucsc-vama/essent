package essent

import essent.BareGraph.NodeID

import collection.mutable.{ArrayBuffer, HashSet}


// TODO: take C_p parameter as input
// TODO: convert back to logging

class AcyclicPart(val mg: MergeGraph, excludeSet: Set[NodeID]) {
  def coarsenWithMFFCs() {
    mg.applyInitialAssignments(MFFC(mg, excludeSet))
  }

  def mergeSingleInputPartsIntoParents(smallZoneCutoff: Int = 20) {
    val singleInputIDs = mg.nodeRange() filter {
      id => (mg.inNeigh(id).size == 1) &&
            (mg.nodeSize(id) < smallZoneCutoff) &&
            (!excludeSet.contains(id))
    }
    val singleInputParents = (singleInputIDs flatMap mg.inNeigh).distinct
    val baseSingleInputIDs = singleInputIDs diff singleInputParents
    println(s"Merging up ${baseSingleInputIDs.size} single-input zones")
    baseSingleInputIDs foreach { childID => {
      val parentID = mg.inNeigh(childID).head
      if (!excludeSet.contains(parentID))
        mg.mergeGroups(parentID, Seq(childID))
    }}
    if (baseSingleInputIDs.size < singleInputIDs.size)
      mergeSingleInputPartsIntoParents(smallZoneCutoff)
  }

  def partition() {
    coarsenWithMFFCs()
    mergeSingleInputPartsIntoParents()
    assert(checkPartioning())
  }

  def iterParts() = mg.iterGroups

  def checkPartioning() = {
    val includedSoFar = HashSet[NodeID]()
    val disjoint = mg.iterGroups forall { case (macroID, memberIDs) => {
      val overlap = includedSoFar.intersect(memberIDs.toSet).nonEmpty
      includedSoFar ++= memberIDs
      !overlap
    }}
    val complete = includedSoFar == mg.nodeRange.toSet
    disjoint && complete
  }
}


object AcyclicPart {
  def apply(og: BareGraph, excludeSet: Set[NodeID] = Set()) = {
    val ap = new AcyclicPart(MergeGraph(og), excludeSet)
    // TODO: what should return type be? a mergegraph?
    ap
  }
}
