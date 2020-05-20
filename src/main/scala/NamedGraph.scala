package essent

import firrtl.ir._

import collection.mutable.{ArrayBuffer, BitSet, HashMap}

// Extends BareGraph to include more attributes per node
//  - Associates a name (String) and Statement with each node
//  - Name must be unique, since can find nodes by name too
//  - Nodes can have an EmptyStatement if no need to emit

class NamedGraph  extends BareGraph {
  // Access companion object's type aliases without prefix
  // TODO: type alias for name type? Hard to imagine other than String?
  import BareGraph.{NodeID, AdjacencyList}

  
  // Internal data structures
  //----------------------------------------------------------------------------
  // Vertex name (string of destination variable) -> numeric ID
  val nameToID = HashMap[String,NodeID]()
  // Numeric vertex ID -> name (string destination variable)
  val idToName = ArrayBuffer[String]()
  // Numeric vertex ID -> firrtl statement (Block used for aggregates)
  val idToStmt = ArrayBuffer[Statement]()
  // Numeric vertex ID -> Boolean indicating whether node should be emitted
  val validNodes = BitSet()


  // Graph building
  //----------------------------------------------------------------------------
  def getID(vertexName: String) = {
    if (nameToID contains vertexName) nameToID(vertexName)
    else {
      val newID = nameToID.size
      nameToID(vertexName) = newID
      idToName += vertexName
      // TODO: is it better to trust BareGraph to grow for new ID? (current)
      newID
    }
  }

  def addEdge(sourceName: String, destName: String) {
    super.addEdge(getID(sourceName), getID(destName))
  }

  def addEdgeIfNew(sourceName: String, destName: String) {
    super.addEdgeIfNew(getID(sourceName), getID(destName))
  }

  def addStatementNode(resultName: String, depNames: Seq[String],
                       stmt: Statement = EmptyStmt) = {
    val potentiallyNewDestID = getID(resultName)
    validNodes += potentiallyNewDestID
    depNames foreach {depName : String => addEdge(depName, resultName)}
    if (potentiallyNewDestID >= idToStmt.size) {
      val numElemsToGrow = potentiallyNewDestID - idToStmt.size + 1
      idToStmt.appendAll(ArrayBuffer.fill(numElemsToGrow)(EmptyStmt))
    }
    idToStmt(potentiallyNewDestID) = stmt
  }


  // Traversal
  //----------------------------------------------------------------------------


  // Stats
  //----------------------------------------------------------------------------
  override def numNodes() = validNodes.size

  def numNodeRefs() = idToName.size  
}
