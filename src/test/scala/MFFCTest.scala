package essent

import collection.mutable.ArrayBuffer

import org.scalatest._

// Test topology, arrows flow left to right
// 0 - 1 - 2
//       /
// 3 - 4 - 5
//
// 6 - 7

class MFFCSpec extends FlatSpec {
  def buildStartingBG() = {
    val bg = new BareGraph()
    bg.addEdge(0,1)
    bg.addEdge(1,2)
    bg.addEdge(3,4)
    bg.addEdge(4,5)
    bg.addEdge(4,2)
    bg.addEdge(6,7)
    bg
  }

  "A MFFC" should "be built from a BareGraph from scratch" in {
    val bg = buildStartingBG()
    val mffc = MFFC(bg)
    assert(mffc == ArrayBuffer(2,2,2,4,4,5,7,7))
  }

  it should "grow initialAssignments appropriately" in {
    val bg = buildStartingBG()
    val mffcWorker = new MFFC(bg)
    val initialMFFC =  ArrayBuffer(-1,-1, 2,-1,-1, 2,-1,-1)
    val expectedMFFC = ArrayBuffer( 2, 2, 2, 2, 2, 2,-1,-1)
    mffcWorker.overideMFFCs(initialMFFC)
    mffcWorker.maximizeFFCs(Set(2,5))
    val grownMFFC = mffcWorker.mffc
    assert(grownMFFC == expectedMFFC)
  }
}
