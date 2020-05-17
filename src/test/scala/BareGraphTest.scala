package essent

import org.scalatest._

class BareGraphSpec extends FlatSpec {
  "A BareGraph" should "grow as necessary for new edges" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    assertResult(2) { bg.numNodes }
    assertResult(1) { bg.numEdges }
    bg.addEdge(2,4)
    assertResult(5) { bg.numNodes }
    assertResult(2) { bg.numEdges }
  }

  it should "not add duplicate edges (if requested)" in {
    val bg = new BareGraph
    bg.addEdgeIfNew(0,1)
    assertResult(2) { bg.numNodes }
    assertResult(1) { bg.numEdges }
    bg.addEdgeIfNew(0,1)
    assertResult(2) { bg.numNodes }
    assertResult(1) { bg.numEdges }
  }

  it should "remove duplicate edges from graph" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    assertResult(2) { bg.numNodes }
    assertResult(1) { bg.numEdges }
    bg.addEdge(0,1)
    assertResult(2) { bg.numNodes }
    assertResult(2) { bg.numEdges }
    bg.removeDuplicateEdges()
    assertResult(2) { bg.numNodes }
    assertResult(1) { bg.numEdges }
  }

  it should "be able to merge nodes mutably" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    bg.addEdge(0,2)
    bg.addEdge(3,4)
    bg.addEdge(3,0)
    bg.mergeNodesMutably(Seq(0,3))
    assert(bg.outNeigh(0).contains(4))
    assert(bg.inNeigh(4).contains(0))
    assert(bg.outNeigh(3).isEmpty)
    assert(bg.inNeigh(3).isEmpty)
    assert(!bg.outNeigh(0).contains(3))
    assert(!bg.inNeigh(0).contains(3))
    assert(!bg.outNeigh(4).contains(3))
    assert(!bg.inNeigh(4).contains(3))
  }
}
