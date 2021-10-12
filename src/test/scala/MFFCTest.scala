package essent

import collection.mutable.ArrayBuffer

import org.scalatest.flatspec.AnyFlatSpec

// Test topology, arrows flow left to right
// 0 - 1 - 2
//       /
// 3 - 4 - 5
//
// 6 - 7

class MFFCSpec extends AnyFlatSpec {
  def buildStartingGraph() = {
    val g = new Graph()
    g.addEdge(0,1)
    g.addEdge(1,2)
    g.addEdge(3,4)
    g.addEdge(4,5)
    g.addEdge(4,2)
    g.addEdge(6,7)
    g
  }

  "A MFFC" should "be built from a Graph from scratch" in {
    val g = buildStartingGraph()
    assertResult(ArrayBuffer(2,2,2,4,4,5,7,7)) { MFFC(g) }
  }

  it should "grow initialAssignments appropriately" in {
    val g = buildStartingGraph()
    val mffcWorker = new MFFC(g)
    val initialMFFC =  ArrayBuffer(-1,-1, 2,-1,-1, 2,-1,-1)
    val expectedMFFC = ArrayBuffer( 2, 2, 2, 2, 2, 2,-1,-1)
    mffcWorker.overrideMFFCs(initialMFFC)
    mffcWorker.maximizeFFCs(Set(2,5))
    assertResult(expectedMFFC) { mffcWorker.mffc }
  }

  it should "be able to prevent MFFCs from including excluded" in {
    val g = buildStartingGraph()
    assertResult(ArrayBuffer(1,1,2,3,4,5,6,7)) { MFFC(g, Set(2,4,6)) }
  }
}
