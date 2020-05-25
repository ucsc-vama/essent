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

  it should "find trivial external paths" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    bg.addEdge(1,2)
    assert( bg.extPathExists(0,2))
    assert(!bg.extPathExists(0,1))
    assert(!bg.extPathExists(2,0))
  }

  it should "find more sophisticated external paths" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    bg.addEdge(0,2)
    bg.addEdge(1,2)
    bg.addEdge(10,11)
    bg.addEdge(10,12)
    assert(!bg.extPathExists(0,10))
    assert(!bg.extPathExists(0,12))
    bg.addEdge(2,11)
    assert( bg.extPathExists(0,11))
    assert(!bg.extPathExists(0,10))
    assert(!bg.extPathExists(0,12))
    assert(!bg.extPathExists(Set(0,1,2),Set(10,11,12)))
    assert( bg.extPathExists(Set(0,1),Set(10,11,12)))
  }

  it should "test safety or merges (whether acyclic)" in {
    val bg = new BareGraph
    bg.addEdge(0,1)
    bg.addEdge(1,2)
    assert( bg.mergeIsAcyclic(0,1))
    assert( bg.mergeIsAcyclic(1,0))
    assert(!bg.mergeIsAcyclic(0,2))
    assert(!bg.mergeIsAcyclic(2,0))
    bg.addEdge(0,2)
    assert(!bg.mergeIsAcyclic(0,2))
    bg.addEdge(10,11)
    assert( bg.mergeIsAcyclic(0,10))
    assert( bg.mergeIsAcyclic(11,0))
  }
}
