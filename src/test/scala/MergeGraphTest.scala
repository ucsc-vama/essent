package essent

import collection.mutable.ArrayBuffer

import org.scalatest._

class MergeGraphSpec extends FlatSpec {
  "A MergeGraph" should "be built from a BareGraph with initialAssignments" in {
    val og = new BareGraph()
    og.addEdge(0,1)
    og.addEdge(0,2)
    og.addEdge(1,2)
    og.addEdge(4,5)
    og.addEdge(4,6)
    og.addEdge(2,5)
    val initialAssignments = ArrayBuffer(1,1,1,3,6,6,6)
    val mg = MergeGraph(og, initialAssignments)
    assert(mg.idToMergeID == initialAssignments)
    assert(mg.mergeIDToMembers == Map(
      (1,Seq(0,1,2)), (3,Seq(3)), (6,Seq(4,5,6))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1) == Seq(6))
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6).isEmpty)
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1).isEmpty)
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3).isEmpty)
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6) == Seq(1))
  }
}
