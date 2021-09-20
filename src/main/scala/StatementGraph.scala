package essent

import firrtl.ir._

import essent.Emitter._
import essent.Extract._
import essent.ir._

import collection.mutable.{ArrayBuffer, BitSet, HashMap}
import scala.reflect.ClassTag

// Extends Graph to include more attributes per node
//  - Associates a name (String) and Statement with each node
//  - Name must be unique, since can find nodes by name too
//  - Nodes can have an EmptyStatement if no need to emit

class StatementGraph extends Graph {
  // Access companion object's type aliases without prefix
  // TODO: type alias for name type? Hard to imagine other than String?
  import Graph.{NodeID, AdjacencyList}


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
      idToStmt += EmptyStmt
      growNeighsIfNeeded(newID)
      // TODO: is it better to trust Graph to grow for new ID? (current)
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
    depNames foreach {depName : String => addEdge(depName, resultName)}
    if (potentiallyNewDestID >= idToStmt.size) {
      val numElemsToGrow = potentiallyNewDestID - idToStmt.size + 1
      idToStmt.appendAll(ArrayBuffer.fill(numElemsToGrow)(EmptyStmt))
    }
    idToStmt(potentiallyNewDestID) = stmt
    // Don't want to emit state element declarations
    if (!stmt.isInstanceOf[DefRegister] && !stmt.isInstanceOf[DefMemory])
      validNodes += potentiallyNewDestID
  }

  def buildFromBodies(bodies: Seq[Statement]) {
    val bodyHE = bodies flatMap {
      case b: Block => b.stmts flatMap findDependencesStmt
      case s => findDependencesStmt(s)
    }
    bodyHE foreach { he => addStatementNode(he.name, he.deps, he.stmt) }
  }


  // Traversal / Queries / Extraction
  //----------------------------------------------------------------------------
  def collectValidStmts(ids: Seq[NodeID]): Seq[Statement] = ids filter validNodes map idToStmt

  def stmtsOrdered(): Seq[Statement] = collectValidStmts(TopologicalSort(this))

  def containsStmtOfType[T <: Statement]()(implicit tag: ClassTag[T]): Boolean = {
    (idToStmt collectFirst { case s: T => s }).isDefined
  }

  def findIDsOfStmtOfType[T <: Statement]()(implicit tag: ClassTag[T]): Seq[NodeID] = {
    idToStmt.zipWithIndex collect { case (s: T , id: Int) => id }
  }

  def allRegDefs(): Seq[DefRegister] = idToStmt collect {
    case dr: DefRegister => dr
  }

  def stateElemNames(): Seq[String] = idToStmt collect {
    case dr: DefRegister => dr.name
    case dm: DefMemory => dm.name
  }

  def stateElemIDs() = findIDsOfStmtOfType[DefRegister] ++ findIDsOfStmtOfType[DefMemory]

  def mergeIsAcyclic(nameA: String, nameB: String): Boolean = {
    val idA = nameToID(nameA)
    val idB = nameToID(nameB)
    super.mergeIsAcyclic(idA, idB)
  }

  def extractSourceIDs(e: Expression): Seq[NodeID] = findDependencesExpr(e) map nameToID


  // Mutation
  //----------------------------------------------------------------------------
  def addOrderingDepsForStateUpdates() {
    def addOrderingEdges(writerID: NodeID, readerTargetID: NodeID) {
      outNeigh(readerTargetID) foreach {
        readerID => if (readerID != writerID) addEdgeIfNew(readerID, writerID)
      }
    }
    idToStmt.zipWithIndex foreach { case(stmt, id) => {
      val readerTargetName = stmt match {
        case ru: RegUpdate => Some(emitExpr(ru.regRef))
        case mw: MemWrite => Some(mw.memName)
        case _ => None
      }
      readerTargetName foreach {
        name => if (nameToID.contains(name)) addOrderingEdges(id, nameToID(name))
      }
    }}
  }

  def mergeStmtsMutably(mergeDest: NodeID, mergeSources: Seq[NodeID], mergeStmt: Statement) {
    val mergedID = mergeDest
    val idsToRemove = mergeSources
    idsToRemove foreach { id => idToStmt(id) = EmptyStmt }
    // NOTE: keeps mappings of name (idToName & nameToID) for debugging dead nodes
    mergeNodesMutably(mergeDest, mergeSources)
    idToStmt(mergeDest) = mergeStmt
    validNodes(mergeDest) = (mergeSources :+ mergeDest) exists { validNodes }
    validNodes --= idsToRemove
  }


  // Stats
  //----------------------------------------------------------------------------
  def numValidNodes() = validNodes.size

  def numNodeRefs() = idToName.size

  def makeStatsString() =
    s"Graph has $numNodes nodes ($numValidNodes valid) and $numEdges edges"
}



object StatementGraph {
  def apply(bodies: Seq[Statement]): StatementGraph = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg.addOrderingDepsForStateUpdates()
    sg
  }

  def apply(circuit: Circuit, removeFlatConnects: Boolean = true): StatementGraph =
    apply(flattenWholeDesign(circuit, removeFlatConnects))
}
