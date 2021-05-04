package essent

import essent.Graph.NodeID
import logger._

import collection.mutable.{ArrayBuffer, HashSet}
import scala.annotation.tailrec


class AcyclicPart(val mg: MergeGraph, excludeSet: collection.Set[NodeID]) extends LazyLogging {
  def partsRemaining() = (mg.mergeIDToMembers.keys.toSet - excludeSet).size

  /*
  def findSmallParts(smallPartCutoff: Int) = mg.mergeIDToMembers.keys.toSeq filter {
    id => (mg.nodeSize(id) < smallPartCutoff) && (!excludeSet.contains(id))
  }*/
  // Map[partitionName:String, Seq[NodeID]]
  def findSmallParts(smallPartCutoff: Int) = mg.mergeIDToMembers.keys
    .groupBy(mg.idToTag)
    .mapValues(_.filter({
      id => (mg.nodeSize(id) < smallPartCutoff) && (!excludeSet.contains(id))
    }).toSeq)

  def perfomMergesIfPossible(mergesToConsider: Seq[Seq[NodeID]]) = {
    val mergesMade = mergesToConsider flatMap { mergeReq => {
      assert(mergeReq.size > 1)
      val partsStillExist = mergeReq.forall { mg.mergeIDToMembers.contains(_) }
      val isAcyclic = mg.mergeIsAcyclic(mergeReq.toSet)
      val isTagSame = mg.mergeIsTagSame(mergeReq.toSet)
      if (partsStillExist && isAcyclic && isTagSame) {
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
    mg.applyInitialAssignments(mffcResults)
    logger.info(s"  #mffcs found: ${mg.mergeIDToMembers.size - excludeSet.size}")
    logger.info(s"  largest mffc: ${(mg.mergeIDToMembers.values.map{_.size}).max}")
  }

  @tailrec
  final def mergeSingleInputPartsIntoParents(smallPartCutoff: Int = 20) {
    val doMore = findSmallParts(smallPartCutoff).exists({ case (tagName, smallPartIDs) => {
      // Executed per partition (tag)
      // TODO: skip the partitions that are already happy
      val singleInputIDs = smallPartIDs filter { id => (mg.inNeigh(id).size == 1) }
      val singleInputParents = (singleInputIDs flatMap mg.inNeigh).distinct
      val baseSingleInputIDs = singleInputIDs diff singleInputParents
      logger.info(s"  merging up ${baseSingleInputIDs.size} single-input parts")
      baseSingleInputIDs foreach { childID => {
        val parentID = mg.inNeigh(childID).head
        if (!excludeSet.contains(parentID) && mg.mergeIsTagSame(parentID, childID))
          mg.mergeGroups(parentID, Seq(childID))
        }
      }
      // Return if there are more to do
      baseSingleInputIDs.size < singleInputIDs.size
    }}) // are there any others left to do?

    if (doMore) mergeSingleInputPartsIntoParents(smallPartCutoff)
  }

  @tailrec
  final def mergeSmallSiblings(smallPartCutoff: Int = 10) {
    val doMore = findSmallParts(smallPartCutoff).exists({ case (tagName, smallPartIDs) => {
      val inputsAndIDPairs = smallPartIDs map { id => {
        val inputsCanonicalized = mg.inNeigh(id).sorted
        (inputsCanonicalized, id)
      }
      }
      val inputsToSiblings = Util.groupByFirst(inputsAndIDPairs.toSeq)
      // NOTE: since inputs *exactly* the same, don't need to do merge safety check
      val mergesToConsider = inputsToSiblings collect {
        case (inputIDs, siblingIDs) if (siblingIDs.size > 1) => siblingIDs
      }
      logger.info(s"  attempting to merge ${mergesToConsider.size} groups of small siblings")
      val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
      mergesMade.nonEmpty // if this is non-empty then do it again
    }})

    if (doMore) mergeSmallSiblings(smallPartCutoff)
  }

  @tailrec
  final def mergeSmallParts(smallPartCutoff: Int = 20, mergeThreshold: Double = 0.5) {
    val doMore = findSmallParts(smallPartCutoff).exists({ case (tagName, smallPartIDs) => {
      val mergesToConsider = smallPartIDs flatMap { id => {
        val numInputs = mg.inNeigh(id).size.toDouble
        val siblings = (mg.inNeigh(id) flatMap mg.outNeigh).distinct - id
        val legalSiblings = siblings filter { sibID => !excludeSet.contains(sibID) && mg.mergeIsTagSame(id, sibID) }
        val orderConstrSibs = legalSiblings filter {
          _ < id
        }
        val myInputSet = mg.inNeigh(id).toSet
        val sibsScored = orderConstrSibs map {
          sibID => (mg.inNeigh(sibID).count(myInputSet) / numInputs, sibID)
        }
        val choices = sibsScored filter {
          _._1 >= mergeThreshold
        }
        val choicesOrdered = choices.sortWith {
          _._1 > _._1
        }
        val topChoice = choicesOrdered.find {
          case (score, sibID) => mg.mergeIsAcyclic(sibID, id) && mg.mergeIsTagSame(sibID, id)
        }
        if (topChoice.isEmpty) Seq()
        else Seq(Seq(topChoice.get._2, id))
      }
      }
      logger.info(s"  of ${smallPartIDs.size} small parts ${mergesToConsider.size} worth merging")
      val mergesMade = perfomMergesIfPossible(mergesToConsider.toSeq)
      mergesMade.nonEmpty
    }})

    if (doMore) mergeSmallParts(smallPartCutoff, mergeThreshold)
  }

  @tailrec
  final def mergeSmallPartsDown(smallPartCutoff: Int = 20) {
    val doMore = findSmallParts(smallPartCutoff).exists({ case (tagName, smallPartIDs) => {
      val mergesToConsider = smallPartIDs flatMap { id => {
        val mergeableChildren = mg.outNeigh(id) filter {
          childID => mg.mergeIsAcyclic(id, childID) && mg.mergeIsTagSame(id, childID) && !excludeSet.contains(childID)
        }
        if (mergeableChildren.nonEmpty) {
          val orderedByEdgesRemoved = mergeableChildren.sortBy {
            childID => numEdgesRemovedByMerge(Seq(id, childID))
          }
          val topChoice = orderedByEdgesRemoved.last
          Seq(Seq(id, topChoice))
        } else Seq()
      }}
      logger.info(s"  of ${smallPartIDs.size} small parts ${mergesToConsider.size} worth merging down")
      val mergesMade = perfomMergesIfPossible(mergesToConsider)
      mergesMade.nonEmpty
    }})

    if (doMore) mergeSmallPartsDown(smallPartCutoff)
  }

  def partition(smallPartCutoff: Int = 20) {
    val toApply = Seq(
      //("mffc", {ap: AcyclicPart => ap.coarsenWithMFFCs()}),
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
      logger.info(s"[$label] took: ${stopTime - startTime}")
      logger.info(s"Down to ${partsRemaining()} parts")
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

    // check that all of the partitions contain the same type of element
    val allTagsSame = mg.iterGroups forall {
      case (macroID, memberIDs) => mg.mergeIsTagSame(memberIDs.toSet + macroID)
    }

    disjoint && complete && allTagsSame
  }
}


object AcyclicPart {
  def apply(g: Graph, excludeSet: collection.Set[NodeID] = Set()) = {
    val ap = new AcyclicPart(MergeGraph(g), excludeSet)
    ap
  }
}
