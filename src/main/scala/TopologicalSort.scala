package essent

import Graph._

import collection.mutable.{ArrayBuffer, BitSet}

object TopologicalSort {
  def apply(g: Graph) = {
    val finalOrdering = ArrayBuffer[NodeID]()
    val inStack = BitSet()
    val finished = BitSet()
    def visit(v: NodeID) {
      if (inStack(v)) {
        findCyclesByTopoSort(g) match {
          case None => throw new Exception("Was a cycle but couldn't reproduce")
          case Some(cycle) => {
            cycle foreach println
            throw new Exception("There is a cycle! (above)")
          }
        }
      } else if (!finished(v)) {
        inStack.add(v)
        g.inNeigh(v) foreach { u => visit(u) }
        finished.add(v)
        inStack.remove(v)
        finalOrdering += v
      }
    }
    g.nodeRange foreach { startingID => visit(startingID) }
    finalOrdering
  }


  def findCyclesByTopoSort(bg: Graph): Option[Seq[NodeID]] = {
    var cycleFound: Option[Seq[NodeID]] = None
    val inStack = BitSet()
    val finished = BitSet()
    val callerIDs = ArrayBuffer.fill(bg.numNodes)(-1)

    def backtrackToFindCycle(v: NodeID, cycleSoFar: Seq[NodeID]): Seq[NodeID] = {
      if (callerIDs(v) == -1) cycleSoFar
      else if (bg.outNeigh(v).forall(!cycleSoFar.contains(_)))
        backtrackToFindCycle(callerIDs(v), cycleSoFar ++ Seq(v))
      else {
        val loopbackIndices = bg.outNeigh(v) map cycleSoFar.indexOf
        val trimmedCycle = cycleSoFar.drop(loopbackIndices.max)
        trimmedCycle ++ Seq(v)
      }
    }

    def visit(v: NodeID, callerID: NodeID) {
      if (inStack(v)) {
        val cycle = backtrackToFindCycle(callerID, Seq(v))
        cycleFound = Some(cycle)
      } else if (!finished(v)) {
        if (v != callerID)
          callerIDs(v) = callerID
        inStack.add(v)
        bg.inNeigh(v) foreach { u => visit(u, v) }
        finished.add(v)
        inStack.remove(v)
      }
    }
    bg.nodeRange foreach { startingID => visit(startingID, startingID) }
    cycleFound
  }
}
