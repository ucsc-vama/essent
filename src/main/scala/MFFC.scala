package essent

import BareGraph._

import collection.mutable.ArrayBuffer


// TODO: add logging back in
// TODO: add support for excluding nodes

class MFFC(val bg: BareGraph) {
  import MFFC.NodeUnreached

  def initialMFFCs(): ArrayBuffer[Int] =  ArrayBuffer.fill(bg.numNodes)(NodeUnreached)

  def findMFFCs(priorMFFC: ArrayBuffer[NodeID]): ArrayBuffer[NodeID] = {
    val unvisitedSinks = bg.nodeRange filter {
      id => priorMFFC(id) == NodeUnreached && bg.outNeigh(id).isEmpty
    }
    val visited = bg.nodeRange filter { id => priorMFFC(id) != NodeUnreached }
    val fringe = (visited flatMap(bg.inNeigh)).distinct
    val unvisitedFringe = fringe filter { priorMFFC(_) == NodeUnreached }
    val newMFFCseeds = unvisitedSinks.toSet ++ unvisitedFringe
    if (newMFFCseeds.isEmpty) {
      priorMFFC
    } else {
      newMFFCseeds foreach { id => priorMFFC(id) = id }
      val nextMFFC = maximizeFFCs(newMFFCseeds, priorMFFC)
      findMFFCs(nextMFFC)
    }
  }

  def maximizeFFCs(fringe: Set[NodeID], mffc: ArrayBuffer[NodeID]): ArrayBuffer[NodeID] = {
    val fringeAncestors = fringe flatMap bg.inNeigh filter { mffc(_) == NodeUnreached }
    val newMembers = fringeAncestors flatMap { parent => {
      val childrenMFFCs = (bg.outNeigh(parent) map mffc).distinct
      if ((childrenMFFCs.size == 1) && (childrenMFFCs.head != NodeUnreached)) {
        mffc(parent) = childrenMFFCs.head
        Seq(parent)
      } else Seq()
    }}
    if (newMembers.isEmpty) mffc
    else maximizeFFCs(newMembers, mffc)
  }
}


object MFFC {
  val NodeUnreached = -1

  def apply(bg: BareGraph): ArrayBuffer[NodeID] = {
    val worker = new MFFC(bg)
    worker.findMFFCs(worker.initialMFFCs)
  }
}

