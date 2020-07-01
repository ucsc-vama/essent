package essent

import collection.mutable.ArrayBuffer

import org.scalatest._


class AcyclicPartSpec extends FlatSpec {
  // Test topology, arrows flow left to right
  // 0 - 1 - 2
  //       /
  // 3 - 4 - 5
  //
  // 6 - 7
  def buildStartingBG1() = {
    val bg = new BareGraph()
    bg.addEdge(0,1)
    bg.addEdge(1,2)
    bg.addEdge(3,4)
    bg.addEdge(4,5)
    bg.addEdge(4,2)
    bg.addEdge(6,7)
    bg
  }

  // Test topology, arrows flow left to right
  // 0 - 1 - 8
  //
  // 2 - 3
  //   \
  //     4
  // 5
  //   \
  // 6 - 7
  def buildStartingBG2() = {
    val bg = new BareGraph()
    bg.addEdge(0,1)
    bg.addEdge(2,3)
    bg.addEdge(2,4)
    bg.addEdge(5,7)
    bg.addEdge(6,7)
    bg.addEdge(1,8)
    bg
  }

  "An AcyclicPart" should "be built from a BareGraph" in {
    val ap = AcyclicPart(buildStartingBG1)
    assertResult(ArrayBuffer(0,1,2,3,4,5,6,7)){ ap.mg.idToMergeID }
  }

  it should "coarsen by MFFCs" in {
    val ap = AcyclicPart(buildStartingBG1)
    ap.coarsenWithMFFCs()
    assertResult(ArrayBuffer(2,2,2,4,4,5,7,7)){ ap.mg.idToMergeID }
  }

  // TODO: should actually test smallZoneCutoff argument
  it should "merge single-input partitions into their parents" in {
    val ap = AcyclicPart(buildStartingBG2)
    ap.mergeSingleInputPartsIntoParents()
    assertResult(ArrayBuffer(0,0,2,2,2,5,6,7,0)){ ap.mg.idToMergeID }
  }

  it should "merge single-input MFFCs with their parents" in {
    val ap = AcyclicPart(buildStartingBG1)
    ap.partition()
    assertResult(ArrayBuffer(4,4,4,4,4,4,7,7)){ ap.mg.idToMergeID }
  }
}
