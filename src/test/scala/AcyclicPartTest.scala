package essent

import collection.mutable.ArrayBuffer

import org.scalatest.flatspec.AnyFlatSpec


class AcyclicPartSpec extends AnyFlatSpec {
  // Test topology, arrows flow left to right
  // 0 - 1 - 2
  //       /
  // 3 - 4 - 5
  //
  // 6 - 7
  def buildStartingGraph1() = {
    val g = new Graph()
    g.addEdge(0,1)
    g.addEdge(1,2)
    g.addEdge(3,4)
    g.addEdge(4,5)
    g.addEdge(4,2)
    g.addEdge(6,7)
    g
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
  def buildStartingGraph2() = {
    val g = new Graph()
    g.addEdge(0,1)
    g.addEdge(2,3)
    g.addEdge(2,4)
    g.addEdge(5,7)
    g.addEdge(6,7)
    g.addEdge(1,8)
    g
  }

  "An AcyclicPart" should "be built from a Graph" in {
    val ap = AcyclicPart(buildStartingGraph1)
    assertResult(ArrayBuffer(0,1,2,3,4,5,6,7)){ ap.mg.idToMergeID }
  }

  it should "coarsen by MFFCs" in {
    val expected = Map((2,Seq(0,1,2)), (4,Seq(3,4)), (5,Seq(5)), (7,Seq(6,7)))
    val ap = AcyclicPart(buildStartingGraph1)
    ap.coarsenWithMFFCs()
    assertResult(ArrayBuffer(2,2,2,4,4,5,7,7)){ ap.mg.idToMergeID }
    assertResult(expected){ ap.iterParts }
  }

  it should "coarsen by MFFCs w/ exclude set" in {
    val expected = Map((1,Seq(0,1)), (2,Seq(2)), (3,Seq(3)), (4,Seq(4)),
                       (5,Seq(5)), (6,Seq(6)), (7,Seq(7)))
    val ap = AcyclicPart(buildStartingGraph1, Set(2,4,6))
    ap.coarsenWithMFFCs()
    assertResult(ArrayBuffer(1,1,2,3,4,5,6,7)){ ap.mg.idToMergeID }
    assertResult(expected){ ap.iterParts }
  }

  // TODO: should actually test smallZoneCutoff argument
  it should "merge single-input partitions into their parents" in {
    val expected = Map((0,Seq(0,1,8)), (2,Seq(2,3,4)), (5,Seq(5)), (6,Seq(6)),
                       (7,Seq(7)))
    val ap = AcyclicPart(buildStartingGraph2)
    ap.mergeSingleInputPartsIntoParents()
    assertResult(ArrayBuffer(0,0,2,2,2,5,6,7,0)){ ap.mg.idToMergeID }
    Util.sortHashMapValues(ap.mg.mergeIDToMembers)
    assertResult(expected){ ap.iterParts }
  }

  it should "merge single-input partitions into their parents w/ exclude set" in {
    val expected = Map((0,Seq(0)), (1,Seq(1,8)), (2,Seq(2,4)), (3,Seq(3)),
                       (5,Seq(5)), (6,Seq(6)), (7,Seq(7)))
    val ap = AcyclicPart(buildStartingGraph2, Set(0,3,6))
    ap.mergeSingleInputPartsIntoParents()
    assertResult(ArrayBuffer(0,1,2,3,2,5,6,7,1)){ ap.mg.idToMergeID }
    assertResult(expected){ ap.iterParts }
  }

  it should "merge single-input MFFCs with their parents" in {
    val expected = Map((4,Seq(0,1,2,3,4,5)), (7,Seq(6,7)))
    val ap = AcyclicPart(buildStartingGraph1)
    ap.coarsenWithMFFCs()
    ap.mergeSingleInputPartsIntoParents()
    assertResult(ArrayBuffer(4,4,4,4,4,4,7,7)){ ap.mg.idToMergeID }
    Util.sortHashMapValues(ap.mg.mergeIDToMembers)
    assertResult(expected){ ap.iterParts }
  }

  it should "merge single-input MFFCs with their parents w/ exclude set" in {
    val expected = Map((0,Seq(0)), (1,Seq(1)), (2,Seq(2)), (4,Seq(3,4,5)),
                       (7,Seq(6,7)))
    val ap = AcyclicPart(buildStartingGraph1, Set(1))
    ap.coarsenWithMFFCs()
    ap.mergeSingleInputPartsIntoParents()
    assertResult(ArrayBuffer(0,1,2,4,4,4,7,7)){ ap.mg.idToMergeID }
    Util.sortHashMapValues(ap.mg.mergeIDToMembers)
    assertResult(expected){ ap.iterParts }
  }
}
