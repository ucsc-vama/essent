package essent

import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// TODO: accept excludeList: HashSet[Int]
// TODO: take C_p parameter as input
// TODO: convert back to logging

class AcyclicPart(val mg: MergeGraph) {
  def coarsenWithMFFCs() {
    mg.applyInitialAssignments(MFFC(mg))
  }

  def mergeSingleInputPartsIntoParents(smallZoneCutoff: Int = 20) {
    val singleInputIDs = mg.nodeRange() filter {
      id => (mg.inNeigh(id).size == 1) && (mg.nodeSize(id) < smallZoneCutoff)
    }
    val singleInputParents = (singleInputIDs flatMap mg.inNeigh).distinct
    val baseSingleInputIDs = singleInputIDs diff singleInputParents
    println(s"Merging up ${baseSingleInputIDs.size} single-input zones")
    baseSingleInputIDs foreach { childID => {
      val parentID = mg.inNeigh(childID).head
      mg.mergeGroups(parentID, Seq(childID))
    }}
    if (baseSingleInputIDs.size < singleInputIDs.size)
      mergeSingleInputPartsIntoParents(smallZoneCutoff)
  }

  def partition() {
    coarsenWithMFFCs()
    mergeSingleInputPartsIntoParents()
  }

  def iterParts() = mg.iterGroups
}


object AcyclicPart {
  def apply(og: BareGraph) = {
    val ap = new AcyclicPart(MergeGraph(og))
    // what should return type be? a mergegraph?
    ap
  }
}
