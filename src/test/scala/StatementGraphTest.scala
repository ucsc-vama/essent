package essent

import firrtl.ir._

import org.scalatest.flatspec.AnyFlatSpec

class StatementGraphSpec extends AnyFlatSpec {
  "A NamedGraph" should "grow as necessary for new edges" in {
    val sg = new StatementGraph
    sg.addEdge("alpha", "beta")
    assertResult(0) { sg.numValidNodes }
    assertResult(2) { sg.numNodeRefs }
    assertResult(1) { sg.numEdges }
    sg.addEdge("gamma", "zeta")
    assertResult(0) { sg.numValidNodes }
    assertResult(4) { sg.numNodeRefs }
    assertResult(2) { sg.numEdges }
  }

  it should "not add duplicate edges (if requested)" in {
    val sg = new StatementGraph
    sg.addEdgeIfNew("alpha", "beta")
    assertResult(0) { sg.numValidNodes }
    assertResult(2) { sg.numNodeRefs }
    assertResult(1) { sg.numEdges }
    sg.addEdgeIfNew("alpha", "beta")
    assertResult(0) { sg.numValidNodes }
    assertResult(2) { sg.numNodeRefs }
    assertResult(1) { sg.numEdges }
  }

  it should "be buildable from hyperedges" in {
    val sg = new StatementGraph
    sg.addStatementNode("child", Seq("parent0","parent1"))
    assertResult(1) { sg.numValidNodes }
    assertResult(3) { sg.numNodeRefs }
    assertResult(2) { sg.numEdges }
    assert(sg.idToStmt(sg.nameToID("child")) == EmptyStmt)
    sg.addStatementNode("sibling", Seq("parent0","parent1"), Block(Seq()))
    assertResult(2) { sg.numValidNodes }
    assertResult(4) { sg.numNodeRefs }
    assertResult(4) { sg.numEdges }
    assert(sg.idToStmt(sg.nameToID("sibling")) == Block(Seq()))
  }

  it should "fill in idToStmts as necessary with EmptyStmt" in {
    val sg = new StatementGraph
    sg.addEdge("alpha", "beta")
    assertResult(EmptyStmt)(sg.idToStmt(sg.nameToID("alpha")))
    sg.addStatementNode("sibling", Seq("parent0","parent1"), Block(Seq()))
    assertResult(EmptyStmt)(sg.idToStmt(sg.nameToID("parent1")))
  }

  it should "test safety or merges (whether acyclic)" in {
    val sg = new StatementGraph
    sg.addEdge("a","b")
    sg.addEdge("b","c")
    assert( sg.mergeIsAcyclic("a","b"))
    assert( sg.mergeIsAcyclic("b","a"))
    assert(!sg.mergeIsAcyclic("a","c"))
    assert(!sg.mergeIsAcyclic("c","a"))
    sg.addEdge("a","c")
    assert(!sg.mergeIsAcyclic("a","c"))
    sg.addEdge("x","y")
    assert( sg.mergeIsAcyclic("a","x"))
    assert( sg.mergeIsAcyclic("y","a"))
  }

  it should "be able to merge Statements" in {
    val sg = new StatementGraph
    sg.addStatementNode("b", Seq("a"), Attach(NoInfo,Seq()))
    sg.addStatementNode("c", Seq("b","a"), Attach(NoInfo,Seq()))
    sg.mergeStmtsMutably(sg.nameToID("b"), Seq(sg.nameToID("c")), Block(Seq()))
    assertResult(Block(Seq()))(sg.idToStmt(sg.nameToID("b")))
    assertResult(EmptyStmt)(sg.idToStmt(sg.nameToID("c")))
    assert( sg.validNodes(sg.nameToID("b")))
    assert(!sg.validNodes(sg.nameToID("c")))
    // trusts Graph's test for mergeNodesMutably
  }

  it should "be able to detect if Statement type anywhere in graph" in {
    val sg = new StatementGraph
    sg.addStatementNode("child", Seq("parent0","parent1"), Block(Seq()))
    assert( sg.containsStmtOfType[Block]())
    assert(!sg.containsStmtOfType[DefWire]())
  }

  it should "find IDs of requested Statement type" in {
    val sg = new StatementGraph
    sg.addStatementNode("child", Seq("parent0","parent1"), Block(Seq()))
    assertResult(Seq(sg.nameToID("child"))) { sg.findIDsOfStmtOfType[Block]() }
    assertResult(Seq()) { sg.findIDsOfStmtOfType[DefWire]() }
  }

  it should "collect valid statements from subset" in {
    val sg = new StatementGraph
    sg.addStatementNode("b", Seq("a"), Attach(NoInfo,Seq()))
    sg.addStatementNode("c", Seq("b","a"), Block(Seq()))
    val goal = Seq(Attach(NoInfo,Seq()), Block(Seq()))
    val result = sg.collectValidStmts(Seq(sg.nameToID("b"), sg.nameToID("c")))
    assertResult(goal.toSet)(result.toSet)
  }

  it should "be able to handle a 1 node graph with no edges" in {
    val stmt = DefNode(NoInfo,"dummy",UIntLiteral(0,IntWidth(1)))
    val sg = StatementGraph(Seq(stmt))
    assertResult(Seq(stmt)) { sg.stmtsOrdered }
  }
}
