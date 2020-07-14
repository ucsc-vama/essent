package essent

import essent.BareGraph.NodeID

import collection.mutable.{ArrayBuffer, HashSet}


// TODO: convert back to logging

class AcyclicPart(val mg: MergeGraph, excludeSet: Set[NodeID]) {
  def partsRemaining() = (mg.mergeIDToMembers.keys.toSet - excludeSet).size

  def findSmallParts(smallPartCutoff: Int) = mg.mergeIDToMembers.keys.toSeq filter {
    id => (mg.nodeSize(id) < smallPartCutoff) && (!excludeSet.contains(id))
  }

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

  def numEdgesRemovedByMerge(mergeReq: Seq[NodeID]): Int = {
    val totalInDegree = (mergeReq map { mg.inNeigh(_).size }).sum
    val totalOutDegree = (mergeReq map { mg.outNeigh(_).size }).sum
    val mergedInDegree = ((mergeReq flatMap mg.inNeigh).distinct diff mergeReq).size
    val mergedOutDegree = ((mergeReq flatMap mg.outNeigh).distinct diff mergeReq).size
    totalInDegree + totalOutDegree - (mergedInDegree + mergedOutDegree)
  }

  def coarsenWithMFFCs() {
    val mffcResults = MFFC(mg, excludeSet)
    excludeSet foreach { id => mffcResults(id) = id }
    mg.applyInitialAssignments(mffcResults)
  }

  def mergeSingleInputPartsIntoParents(smallPartCutoff: Int = 20) {
    val smallPartIDs = findSmallParts(smallPartCutoff)
    val singleInputIDs = smallPartIDs filter { id => (mg.inNeigh(id).size == 1) }
    val singleInputParents = (singleInputIDs flatMap mg.inNeigh).distinct
    val baseSingleInputIDs = singleInputIDs diff singleInputParents
    println(s"  merging up ${baseSingleInputIDs.size} single-input zones")
    baseSingleInputIDs foreach { childID => {
      val parentID = mg.inNeigh(childID).head
      if (!excludeSet.contains(parentID))
        mg.mergeGroups(parentID, Seq(childID))
    }}
    if (baseSingleInputIDs.size < singleInputIDs.size)
      mergeSingleInputPartsIntoParents(smallPartCutoff)
  }

  def mergeSmallSiblings(smallPartCutoff: Int = 10) {
    val smallPartIDs = findSmallParts(smallPartCutoff)
    val inputsAndIDPairs = smallPartIDs map { id => {
      val inputsCanonicalized = mg.inNeigh(id).toSeq.sorted
      (inputsCanonicalized, id)
    }}
    val inputsToSiblings = Util.groupByFirst(inputsAndIDPairs.toSeq)
    // NOTE: since inputs *exactly* the same, don't need to do merge safety check
    val mergesToConsider = inputsToSiblings collect {
      case (inputIDs, siblingIDs) if (siblingIDs.size > 1) => siblingIDs
    }
    println(s"  attempting to merge ${mergesToConsider.size} groups of small siblings")
    val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
    if (mergesMade.nonEmpty) {
      mergeSmallSiblings(smallPartCutoff)
    }
  }

  def mergeSmallParts(smallPartCutoff: Int = 20, mergeThreshold: Double = 0.5) {
    val smallPartIDs = findSmallParts(smallPartCutoff)
    val mergesToConsider = smallPartIDs flatMap { id => {
      val numInputs = mg.inNeigh(id).size.toDouble
      val siblings = (mg.inNeigh(id) flatMap mg.outNeigh).distinct - id
      val legalSiblings = siblings filter { sibID => !excludeSet.contains(sibID) }
      val myInputSet = mg.inNeigh(id).toSet
      val sibsScored = legalSiblings map {
        sibID => (mg.inNeigh(sibID).count(myInputSet) / numInputs, sibID)
      }
      val choices = sibsScored filter { _._1 >= mergeThreshold }
      val choicesOrdered = choices.sortWith{_._1 > _._1}
      val topChoice = choicesOrdered.find {
        case (score, sibID) => mg.mergeIsAcyclic(sibID, id)
      }
      if (topChoice.isEmpty) Seq()
      else Seq(Seq(topChoice.get._2, id))
    }}
    println(s"  of ${smallPartIDs.size} small parts ${mergesToConsider.size} worth merging")
    val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
    if (mergesMade.nonEmpty) {
      mergeSmallParts(smallPartCutoff, mergeThreshold)
    }
  }

  def mergeSmallPartsDown(smallPartCutoff: Int = 20) {
    val smallPartIDs = findSmallParts(smallPartCutoff)
    val mergesToConsider = smallPartIDs flatMap { id => {
      val mergeableChildren = mg.outNeigh(id) filter {
        childID => mg.mergeIsAcyclic(id, childID) && !excludeSet.contains(childID)
      }
      if (mergeableChildren.nonEmpty) {
        val orderedByEdgesRemoved = mergeableChildren.sortBy {
          childID => numEdgesRemovedByMerge(Seq(id, childID))
        }
        val topChoice = orderedByEdgesRemoved.last
        Seq(Seq(id, topChoice))
      } else Seq()
    }}
    println(s"  of ${smallPartIDs.size} small parts ${mergesToConsider.size} worth merging down")
    val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
    if (mergesMade.nonEmpty) {
      mergeSmallPartsDown(smallPartCutoff)
    }
  }

  def partition(smallPartCutoff: Int = 20) {
    val toApply = Seq(
      ("mffc", {ap: AcyclicPart => ap.coarsenWithMFFCs()}),
      ("single", {ap: AcyclicPart => ap.mergeSingleInputPartsIntoParents()}),
      ("siblings", {ap: AcyclicPart => ap.mergeSmallSiblings(smallPartCutoff)}),
      ("small", {ap: AcyclicPart => ap.mergeSmallParts(smallPartCutoff, 0.5)}),
      ("down", {ap: AcyclicPart => ap.mergeSmallPartsDown(smallPartCutoff)}),
      ("small2", {ap: AcyclicPart => ap.mergeSmallParts(2*smallPartCutoff, 0.25)}),
    )
    toApply foreach { case (label, func) => {
      val startTime = System.currentTimeMillis()
      func(this)
      val stopTime = System.currentTimeMillis()
      println(s"[$label] took: ${stopTime - startTime}")
      println(s"Down to ${partsRemaining()} parts")
    }}
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
    ap
  }
}
