package essent

import collection.mutable.ArrayBuffer

import org.scalatest.flatspec.AnyFlatSpec

class MergeGraphSpec extends AnyFlatSpec {
  val initialAssignments = ArrayBuffer(1,1,1,3,4,6,6)

  def buildStartingGraph() = {
    val g = new Graph()
    g.addEdge(0,1)
    g.addEdge(0,2)
    g.addEdge(1,2)
    g.addEdge(5,6)
    g.addEdge(2,5)
    g.addEdge(5,3)
    g
  }

  def buildStartingMG() = MergeGraph(buildStartingGraph(), initialAssignments)

  "A MergeGraph" should "be built from a Graph with initialAssignments" in {
    val mg = MergeGraph(buildStartingGraph(), initialAssignments)
    assert(mg.idToMergeID == initialAssignments)
    assert(mg.iterGroups == Map(
      (1,Seq(0,1,2)), (3,Seq(3)), (4,Seq(4)), (6,Seq(5,6))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1) == Seq(6))
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6) == Seq(3))
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1).isEmpty)
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3) == Seq(6))
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6) == Seq(1))
  }

  it should "be able to apply initialAssignments later" in {
    val mg = MergeGraph(buildStartingGraph())
    mg.applyInitialAssignments(initialAssignments)
    assert(mg.idToMergeID == initialAssignments)
    assert(mg.iterGroups == Map(
      (1,Seq(0,1,2)), (3,Seq(3)), (4,Seq(4)), (6,Seq(5,6))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1) == Seq(6))
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6) == Seq(3))
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1).isEmpty)
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3) == Seq(6))
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6) == Seq(1))
  }

  it should "be able to merge nodes" in {
    val mg = buildStartingMG()
    mg.mergeGroups(6, Seq(1))
    assert(mg.idToMergeID == ArrayBuffer(6,6,6,3,4,6,6))
    assert(mg.iterGroups == Map(
      (3,Seq(3)), (4,Seq(4)), (6,Seq(5,6,0,1,2))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1).isEmpty)
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6) == Seq(3))
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1).isEmpty)
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3) == Seq(6))
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6).isEmpty)
  }

  it should "be able to merge nodes #2" in {
    // Note: merge induces a cycle :(
    val mg = buildStartingMG()
    mg.mergeGroups(1, Seq(3))
    assert(mg.idToMergeID == ArrayBuffer(1,1,1,1,4,6,6))
    assert(mg.iterGroups == Map(
      (1,Seq(0,1,2,3)), (4,Seq(4)), (6,Seq(5,6))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1) == Seq(6))
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6) == Seq(1))
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1) == Seq(6))
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3).isEmpty)
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6) == Seq(1))
  }

  it should "be able to merge with an empty node" in {
    val mg = buildStartingMG()
    mg.mergeGroups(1, Seq(4))
    assert(mg.idToMergeID == ArrayBuffer(1,1,1,3,1,6,6))
    assert(mg.iterGroups == Map(
      (1,Seq(0,1,2,4)), (3,Seq(3)), (6,Seq(5,6))))
    assert(mg.outNeigh(0).isEmpty)
    assert(mg.outNeigh(1) == Seq(6))
    assert(mg.outNeigh(2).isEmpty)
    assert(mg.outNeigh(3).isEmpty)
    assert(mg.outNeigh(4).isEmpty)
    assert(mg.outNeigh(5).isEmpty)
    assert(mg.outNeigh(6) == Seq(3))
    assert(mg.inNeigh(0).isEmpty)
    assert(mg.inNeigh(1).isEmpty)
    assert(mg.inNeigh(2).isEmpty)
    assert(mg.inNeigh(3) == Seq(6))
    assert(mg.inNeigh(4).isEmpty)
    assert(mg.inNeigh(5).isEmpty)
    assert(mg.inNeigh(6) == Seq(1))
  }

  it should "be able to tell size of merged nodes" in {
    val mg = buildStartingMG()
    mg.mergeGroups(6, Seq(1))
    assertResult(0){ mg.nodeSize(0) }
    assertResult(0){ mg.nodeSize(1) }
    assertResult(0){ mg.nodeSize(2) }
    assertResult(1){ mg.nodeSize(3) }
    assertResult(1){ mg.nodeSize(4) }
    assertResult(0){ mg.nodeSize(5) }
    assertResult(5){ mg.nodeSize(6) }
    assertResult(0){ mg.nodeSize(7) }
  }
}
