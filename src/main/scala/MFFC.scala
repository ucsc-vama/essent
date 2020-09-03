package essent

import Graph._

import collection.mutable.ArrayBuffer


class MFFC(val g: Graph) {
  import MFFC.{Unclaimed,Excluded}

  // numeric vertex ID -> MFFC ID
  val mffc = ArrayBuffer.fill(g.numNodes)(Unclaimed)

  def overrideMFFCs(newAssignments: ArrayBuffer[NodeID]) {
    mffc.clear()
    newAssignments.copyToBuffer(mffc)
  }

  def findMFFCs(): ArrayBuffer[NodeID] = {
    val unvisitedSinks = g.nodeRange filter {
      id => mffc(id) == Unclaimed && g.outNeigh(id).isEmpty
    }
    val visited = g.nodeRange filter { id => mffc(id) != Unclaimed }
    val fringe = (visited flatMap(g.inNeigh)).distinct
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
    val fringeAncestors = fringe flatMap g.inNeigh filter { mffc(_) == Unclaimed }
    val newMembers = fringeAncestors flatMap { parent => {
      val childrenMFFCs = (g.outNeigh(parent) map mffc).distinct
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

  def apply(g: Graph, excludeSet: Set[NodeID] = Set()): ArrayBuffer[NodeID] = {
    val worker = new MFFC(g)
    excludeSet foreach { id => worker.mffc(id) = Excluded }
    val mffc = worker.findMFFCs()
    excludeSet foreach { id => mffc(id) = id }
    mffc
  }
}
