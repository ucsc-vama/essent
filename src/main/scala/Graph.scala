package essent

import collection.mutable.{ArrayBuffer, HashMap}

class Graph {
  // Vertex name (string of destination variable) -> numeric ID
  val nameToID = HashMap[String,Int]()
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh = ArrayBuffer[ArrayBuffer[Int]]()

  def getID(vertexName: String) = {
    if (nameToID contains vertexName) nameToID(vertexName)
    else {
      val newID = nameToID.size
      nameToID(vertexName) = newID
      inNeigh += ArrayBuffer[Int]()
      outNeigh += ArrayBuffer[Int]()
      newID
    }
  }

  // adds directed edge
  def addEdge(source:String, dest:String) {
    outNeigh(getID(source)) += getID(dest)
    inNeigh(getID(dest)) += getID(source)
  }
}
