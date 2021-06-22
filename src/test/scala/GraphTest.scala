package essent

import org.scalatest.flatspec.AnyFlatSpec

class GraphSpec extends AnyFlatSpec {
  "A Graph" should "grow as necessary for new edges" in {
    val g = new Graph
    g.addEdge(0,1)
    assertResult(2) { g.numNodes }
    assertResult(1) { g.numEdges }
    g.addEdge(2,4)
    assertResult(5) { g.numNodes }
    assertResult(2) { g.numEdges }
  }

  it should "not add duplicate edges (if requested)" in {
    val g = new Graph
    g.addEdgeIfNew(0,1)
    assertResult(2) { g.numNodes }
    assertResult(1) { g.numEdges }
    g.addEdgeIfNew(0,1)
    assertResult(2) { g.numNodes }
    assertResult(1) { g.numEdges }
  }

  it should "remove duplicate edges from graph" in {
    val g = new Graph
    g.addEdge(0,1)
    assertResult(2) { g.numNodes }
    assertResult(1) { g.numEdges }
    g.addEdge(0,1)
    assertResult(2) { g.numNodes }
    assertResult(2) { g.numEdges }
    g.removeDuplicateEdges()
    assertResult(2) { g.numNodes }
    assertResult(1) { g.numEdges }
  }

  it should "be able to merge nodes mutably" in {
    val g = new Graph
    g.addEdge(0,1)
    g.addEdge(0,2)
    g.addEdge(3,4)
    g.addEdge(3,0)
    g.mergeNodesMutably(0,Seq(3))
    assert(g.outNeigh(0).contains(4))
    assert(g.inNeigh(4).contains(0))
    assert(g.outNeigh(3).isEmpty)
    assert(g.inNeigh(3).isEmpty)
    assert(!g.outNeigh(0).contains(0))
    assert(!g.inNeigh(0).contains(0))
    assert(!g.outNeigh(0).contains(3))
    assert(!g.inNeigh(0).contains(3))
    assert(!g.outNeigh(4).contains(3))
    assert(!g.inNeigh(4).contains(3))
  }

  it should "find trivial external paths" in {
    val g = new Graph
    g.addEdge(0,1)
    g.addEdge(1,2)
    assert( g.extPathExists(0,2))
    assert(!g.extPathExists(0,1))
    assert(!g.extPathExists(2,0))
  }

  it should "find more sophisticated external paths" in {
    val g = new Graph
    g.addEdge(0,1)
    g.addEdge(0,2)
    g.addEdge(1,2)
    g.addEdge(10,11)
    g.addEdge(10,12)
    assert(!g.extPathExists(0,10))
    assert(!g.extPathExists(0,12))
    g.addEdge(2,11)
    assert( g.extPathExists(0,11))
    assert(!g.extPathExists(0,10))
    assert(!g.extPathExists(0,12))
    assert(!g.extPathExists(Set(0,1,2),Set(10,11,12)))
    assert( g.extPathExists(Set(0,1),Set(10,11,12)))
  }

  it should "test safety of 2-node merge" in {
    val g = new Graph
    g.addEdge(0,1)
    g.addEdge(1,2)
    assert( g.mergeIsAcyclic(0,1))
    assert( g.mergeIsAcyclic(1,0))
    assert(!g.mergeIsAcyclic(0,2))
    assert(!g.mergeIsAcyclic(2,0))
    g.addEdge(0,2)
    assert(!g.mergeIsAcyclic(0,2))
    g.addEdge(10,11)
    assert( g.mergeIsAcyclic(0,10))
    assert( g.mergeIsAcyclic(11,0))
  }

  it should "test safety of general merge" in {
    val g = new Graph
    g.addEdge(0,1)
    g.addEdge(1,2)
    assert( g.mergeIsAcyclic(Set(0,1)))
    assert( g.mergeIsAcyclic(Set(1,2)))
    assert(!g.mergeIsAcyclic(Set(0,2)))
    g.addEdge(0,2)
    assert( g.mergeIsAcyclic(Set(0,1)))
    assert( g.mergeIsAcyclic(Set(1,2)))
    assert(!g.mergeIsAcyclic(Set(0,2)))
    assert( g.mergeIsAcyclic(Set(0,1,2)))
    g.addEdge(0,3)
    g.addEdge(3,2)
    assert(!g.mergeIsAcyclic(Set(0,1,2)))
  }
}
