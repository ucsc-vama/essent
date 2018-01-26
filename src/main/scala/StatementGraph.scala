package essent

import firrtl._
import firrtl.ir._

import essent.Extract._

import collection.mutable.ArrayBuffer

class StatementGraph extends Graph {
  // Vertex ID -> firrtl statement (Block used for aggregates)
  val idToStmt = ArrayBuffer[Statement]()

  // make sure idToStmt is as big as needed and tracks id of internal graph
  override def getID(vertexName: String) = {
    val id = super.getID(vertexName)
    while (id >= idToStmt.size)
      idToStmt += EmptyStmt
    id
  }

  def buildFromBodies(bodies: Seq[Statement]) {
    // FUTURE: does bodies contain blocks? should it not after first level?
    bodies foreach {
      case b: Block => {
        val bodyHE = b.stmts flatMap findDependencesStmt
        bodyHE foreach { he => {
          addNodeWithDeps(he.name, he.deps)
          idToStmt(getID(he.name)) = he.stmt
        }}
      }
      case _ => throw new Exception("module level wasn't a Body Statement")      
    }
  }

  def stmtsOrdered(): Seq[Statement] = {
    topologicalSort filter validNodes map idToStmt
  }
}
