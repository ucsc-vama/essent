package essent

import essent.BareGraph.NodeID

import collection.mutable.{ArrayBuffer, HashSet}


// TODO: take C_p parameter as input
// TODO: convert back to logging

class AcyclicPart(val mg: MergeGraph, excludeSet: Set[NodeID]) {
  def perfomMergesIfPossible(mergesToConsider: Seq[Seq[NodeID]]) = {
    val mergesMade = mergesToConsider flatMap { mergeReq => {
      assert(mergeReq.size > 1)
      val partsStillExist = mergeReq.forall{ mg.mergeIDToMembers.contains(_) }
      if (partsStillExist && mg.mergeIsAcyclic(mergeReq.toSet)) {
        assert(mergeReq forall { id => !excludeSet.contains(id) })
        mg.mergeGroups(mergeReq.head, mergeReq.tail)
        Seq(mergeReq)
      } else Seq()
    }}
    mergesMade
  }

  def coarsenWithMFFCs() {
    val mffcResults = MFFC(mg, excludeSet)
    excludeSet foreach { id => mffcResults(id) = id }
    mg.applyInitialAssignments(mffcResults)
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

  def mergeSmallSiblings(smallZoneCutoff: Int = 10) {
    val smallPartIDs = mg.nodeRange filter {
      id => (mg.nodeSize(id) < smallZoneCutoff) && (!excludeSet.contains(id))
    }
    val inputsAndIDPairs = smallPartIDs map { id => {
      val inputsCanonicalized = mg.inNeigh(id).toSeq.sorted
      (inputsCanonicalized, id)
    }}
    val inputsToSiblings = Util.groupByFirst(inputsAndIDPairs.toSeq)
    val mergesToConsider = inputsToSiblings collect {
      case (inputIDs, siblingIDs) if ((siblingIDs.size > 1) && mg.mergeIsAcyclic(siblingIDs.toSet)) => siblingIDs
    }
    println(s"Attempting to merge ${mergesToConsider.size} groups of small siblings")
    val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
    if (mergesMade.nonEmpty) {
      mergeSmallSiblings(smallZoneCutoff)
    }
  }

  def partition() {
    coarsenWithMFFCs()
    mergeSingleInputPartsIntoParents()
    mergeSmallSiblings()
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
    ap.partition()
    // TODO: what should return type be? a mergegraph?
    ap
  }
}
