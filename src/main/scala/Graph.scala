package essent

import collection.mutable.{ArrayBuffer, HashMap}

class Graph {
  // Vertex name (string of destination variable) -> numeric ID
  val nameToID = HashMap[String,Int]()
  // Numeric vertex ID -> name (string destination variable)
  val idToName = ArrayBuffer[String]()
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // Vertex name -> full C++ string it corresponds to
  val nameToCmd = HashMap[String,String]()

  def getID(vertexName: String) = {
    if (nameToID contains vertexName) nameToID(vertexName)
    else {
      val newID = nameToID.size
      nameToID(vertexName) = newID
      idToName += vertexName
      inNeigh += ArrayBuffer[Int]()
      outNeigh += ArrayBuffer[Int]()
      newID
    }
  }

  // adds directed edge
  def addEdge(source: String, dest: String) {
    outNeigh(getID(source)) += getID(dest)
    inNeigh(getID(dest)) += getID(source)
  }

  def addNodeWithDeps(result: String, deps: Seq[String], cmd: String) = {
    nameToCmd(result) = cmd
    deps foreach {dep : String => addEdge(dep, result)}
  }

  override def toString: String = {
    nameToID map {case (longName: String, id: Int) =>
      longName + ": " + inNeigh(id).map{n:Int => idToName(n)}.toSeq.mkString(" ")
    } mkString("\n")
  }

  def topologicalSort() = {
    val finalOrdering = ArrayBuffer[Int]()
    val temporaryMarks = ArrayBuffer.fill(nameToID.size)(false)
    val finalMarks = ArrayBuffer.fill(nameToID.size)(false)
    def visit(vertexID: Int) {
      if (temporaryMarks(vertexID)) throw new Exception("There is a cycle!")
      else if (!finalMarks(vertexID)) {
        temporaryMarks(vertexID) = true
        outNeigh(vertexID) foreach { neighborID => visit(neighborID) }
        finalMarks(vertexID) = true
        temporaryMarks(vertexID) = false
        finalOrdering += vertexID
      }
    }
    nameToID.values foreach {startingID => visit(startingID)}
    finalOrdering.reverse
  }

  def reorderCommands() = {
    val orderedResults = topologicalSort map idToName
    orderedResults filter {nameToCmd.contains} map nameToCmd
  }
}
