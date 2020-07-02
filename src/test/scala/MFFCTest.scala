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
    assertResult(ArrayBuffer(2,2,2,4,4,5,7,7)) { MFFC(bg) }
  }

  it should "grow initialAssignments appropriately" in {
    val bg = buildStartingBG()
    val mffcWorker = new MFFC(bg)
    val initialMFFC =  ArrayBuffer(-1,-1, 2,-1,-1, 2,-1,-1)
    val expectedMFFC = ArrayBuffer( 2, 2, 2, 2, 2, 2,-1,-1)
    mffcWorker.overrideMFFCs(initialMFFC)
    mffcWorker.maximizeFFCs(Set(2,5))
    assertResult(expectedMFFC) { mffcWorker.mffc }
  }

  it should "be able to prevent MFFCs from including excluded" in {
    val bg = buildStartingBG()
    assertResult(ArrayBuffer(1,1,2,3,4,5,6,7)) { MFFC(bg, Set(2,4,6)) }
  }
}
