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

  it should "be able to merge Statements" in {
    val ng = new NamedGraph
    ng.addStatementNode("b", Seq("a"), Attach(NoInfo,Seq()))
    ng.addStatementNode("c", Seq("b","a"), Attach(NoInfo,Seq()))
    ng.mergeStmtsMutably(ng.nameToID("b"), Seq(ng.nameToID("c")), Block(Seq()))
    assertResult(Block(Seq()))(ng.idToStmt(ng.nameToID("b")))
    assertResult(EmptyStmt)(ng.idToStmt(ng.nameToID("c")))
    assert( ng.validNodes(ng.nameToID("b")))
    assert(!ng.validNodes(ng.nameToID("c")))
    // trusts BareGraph's test for mergeNodesMutably
  }

  it should "be able to detect if Statement type anywhere in graph" in {
    val ng = new NamedGraph
    ng.addStatementNode("child", Seq("parent0","parent1"), Block(Seq()))
    assert( ng.containsStmtOfType[Block]())
    assert(!ng.containsStmtOfType[DefWire]())
  }

  it should "find IDs of requested Statement type" in {
    val ng = new NamedGraph
    ng.addStatementNode("child", Seq("parent0","parent1"), Block(Seq()))
    assertResult(Seq(ng.nameToID("child"))) { ng.findIDsOfStmtOfType[Block]() }
    assertResult(Seq()) { ng.findIDsOfStmtOfType[DefWire]() }
  }

  it should "collect valid statements from subset" in {
    val ng = new NamedGraph
    ng.addStatementNode("b", Seq("a"), Attach(NoInfo,Seq()))
    ng.addStatementNode("c", Seq("b","a"), Block(Seq()))
    val goal = Seq(Attach(NoInfo,Seq()), Block(Seq()))
    val result = ng.collectValidStmts(Seq(ng.nameToID("b"), ng.nameToID("c")))
    assertResult(goal.toSet)(result.toSet)
  }
}
