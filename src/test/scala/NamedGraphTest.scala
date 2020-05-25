package essent

import firrtl.ir._

import org.scalatest._

class NamedGraphSpec extends FlatSpec {
  "A NamedGraph" should "grow as necessary for new edges" in {
    val ng = new NamedGraph
    ng.addEdge("alpha", "beta")
    assertResult(0) { ng.numValidNodes }
    assertResult(2) { ng.numNodeRefs }
    assertResult(1) { ng.numEdges }
    ng.addEdge("gamma", "zeta")
    assertResult(0) { ng.numValidNodes }
    assertResult(4) { ng.numNodeRefs }
    assertResult(2) { ng.numEdges }
  }

  it should "not add duplicate edges (if requested)" in {
    val ng = new NamedGraph
    ng.addEdgeIfNew("alpha", "beta")
    assertResult(0) { ng.numValidNodes }
    assertResult(2) { ng.numNodeRefs }
    assertResult(1) { ng.numEdges }
    ng.addEdgeIfNew("alpha", "beta")
    assertResult(0) { ng.numValidNodes }
    assertResult(2) { ng.numNodeRefs }
    assertResult(1) { ng.numEdges }
  }

  it should "be buildable from hyperedges" in {
    val ng = new NamedGraph
    ng.addStatementNode("child", Seq("parent0","parent1"))
    assertResult(1) { ng.numValidNodes }
    assertResult(3) { ng.numNodeRefs }
    assertResult(2) { ng.numEdges }
    assert(ng.idToStmt(ng.nameToID("child")) == EmptyStmt)
    ng.addStatementNode("sibling", Seq("parent0","parent1"), Block(Seq()))
    assertResult(2) { ng.numValidNodes }
    assertResult(4) { ng.numNodeRefs }
    assertResult(4) { ng.numEdges }
    assert(ng.idToStmt(ng.nameToID("sibling")) == Block(Seq()))
  }

  it should "fill in idToStmts as necessary with EmptyStmt" in {
    val ng = new NamedGraph
    ng.addEdge("alpha", "beta")
    assertResult(EmptyStmt)(ng.idToStmt(ng.nameToID("alpha")))
    ng.addStatementNode("sibling", Seq("parent0","parent1"), Block(Seq()))
    assertResult(EmptyStmt)(ng.idToStmt(ng.nameToID("parent1")))
  }

  it should "test safety or merges (whether acyclic)" in {
    val ng = new NamedGraph
    ng.addEdge("a","b")
    ng.addEdge("b","c")
    assert( ng.mergeIsAcyclic("a","b"))
    assert( ng.mergeIsAcyclic("b","a"))
    assert(!ng.mergeIsAcyclic("a","c"))
    assert(!ng.mergeIsAcyclic("c","a"))
    ng.addEdge("a","c")
    assert(!ng.mergeIsAcyclic("a","c"))
    ng.addEdge("x","y")
    assert( ng.mergeIsAcyclic("a","x"))
    assert( ng.mergeIsAcyclic("y","a"))
  }
}
