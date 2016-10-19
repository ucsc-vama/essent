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

  def addNodeWithDeps(result: String, deps: Seq[String]) = {
    deps foreach {dep : String => addEdge(dep, result)}
  }

  override def toString: String = {
    nameToID map {case (longName: String, id: Int) =>
      longName + ": " + inNeigh(id).map{n:Int => idToName(n)}.toSeq.mkString(" ")
    } mkString("\n")
  }
}
