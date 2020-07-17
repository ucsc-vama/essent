package essent

import BareGraph._

import collection.mutable.ArrayBuffer


// TODO: add logging back in

class MFFC(val bg: BareGraph) {
  import MFFC.{Unclaimed,Excluded}

  // numeric vertex ID -> MFFC ID
  val mffc = ArrayBuffer.fill(bg.numNodes)(Unclaimed)

  def overrideMFFCs(newAssignments: ArrayBuffer[NodeID]) {
    mffc.clear()
    newAssignments.copyToBuffer(mffc)
  }

  def findMFFCs(): ArrayBuffer[NodeID] = {
    val unvisitedSinks = bg.nodeRange filter {
      id => mffc(id) == Unclaimed && bg.outNeigh(id).isEmpty
    }
    val visited = bg.nodeRange filter { id => mffc(id) != Unclaimed }
    val fringe = (visited flatMap(bg.inNeigh)).distinct
    val unvisitedFringe = fringe filter { mffc(_) == Unclaimed }
    val newMFFCseeds = unvisitedSinks.toSet ++ unvisitedFringe
    if (newMFFCseeds.isEmpty) {
      mffc
    } else {
      newMFFCseeds foreach { id => mffc(id) = id }
      maximizeFFCs(newMFFCseeds)
      findMFFCs()
    }
  }

  def maximizeFFCs(fringe: Set[NodeID]) {
    val fringeAncestors = fringe flatMap bg.inNeigh filter { mffc(_) == Unclaimed }
    val newMembers = fringeAncestors flatMap { parent => {
      val childrenMFFCs = (bg.outNeigh(parent) map mffc).distinct
      if ((childrenMFFCs.size == 1) && (childrenMFFCs.head != Unclaimed)) {
        mffc(parent) = childrenMFFCs.head
        Seq(parent)
      } else Seq()
    }}
    if (newMembers.nonEmpty)
      maximizeFFCs(newMembers)
  }
}


object MFFC {
  val Unclaimed = -1
  val Excluded  = -2

  def apply(bg: BareGraph, excludeSet: Set[NodeID] = Set()): ArrayBuffer[NodeID] = {
    val worker = new MFFC(bg)
    excludeSet foreach { id => worker.mffc(id) = Excluded }
    val mffc = worker.findMFFCs()
    excludeSet foreach { id => mffc(id) = id }
    mffc
  }
}
