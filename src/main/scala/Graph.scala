package essent

import collection.mutable.{ArrayBuffer, HashMap}
import scala.util.Random


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
    val potentiallyNewDestID = getID(result)
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
      if (temporaryMarks(vertexID)){
        printCycle(temporaryMarks)
        throw new Exception("There is a cycle!")
      } else if (!finalMarks(vertexID)) {
        temporaryMarks(vertexID) = true
        inNeigh(vertexID) foreach { neighborID => visit(neighborID) }
        finalMarks(vertexID) = true
        temporaryMarks(vertexID) = false
        finalOrdering += vertexID
      }
    }
    nameToID.values foreach {startingID => visit(startingID)}
    finalOrdering
  }

  def printCycle(temporaryMarks: ArrayBuffer[Boolean]) {
    (0 until nameToID.size) foreach {id: Int =>
      if (temporaryMarks(id)) {
        println(nameToCmd(idToName(id)))
        println(id + " "  + outNeigh(id))
      }
    }
  }

  def reorderCommands() = {
    val orderedResults = topologicalSort map idToName
    orderedResults filter {nameToCmd.contains} map nameToCmd
  }

  def printTopologyStats() {
    println(s"Nodes: ${nameToCmd.size}")
    println(s"Referenced Nodes: ${idToName.size}")
    val allDegrees = outNeigh map { _.size }
    val totalRefs = allDegrees reduceLeft { _+_ }
    println(s"Total References: $totalRefs")
    val maxDegree = allDegrees reduceLeft { math.max(_,_) }
    val maxDegreeName = idToName(allDegrees.indexOf(maxDegree))
    println(s"Max Degree: $maxDegree ($maxDegreeName)")
    println(s"Approximate Diameter: ${approxDiameter()}")
    val numberOfSinks: Int = (inNeigh map { _.size } filter { _ == 0}).size
    println(s"Number of Sinks: $numberOfSinks")
  }

  def approxDiameter(numTrials: Int = 64) = {
    val numNodes = nameToID.size
    val maxPaths = (0 until numTrials) map { trialNumber =>
      val source = Random.nextInt(numNodes)
      val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
      startingDepths(source) = 0
      val depths = stepBFS(0, startingDepths)
      val maxDepth = depths reduceLeft { math.max(_,_) }
      (maxDepth, s"${idToName(source)} -> ${idToName(depths.indexOf(maxDepth))}")
    }
    val longestPath = maxPaths.sortWith {_._1 < _._1 }.last
    println(s"Longest Path Found: ${longestPath._2}")
    longestPath._1
  }

  def stepBFS(currDepth: Int, allDepths: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    allDepths.zipWithIndex foreach { case(depth, id) => {
      if (depth == currDepth) outNeigh(id).foreach { outNeigh =>
        if (allDepths(outNeigh) == -1) allDepths(outNeigh) = currDepth + 1
      }
    }}
    if (allDepths.contains(currDepth+1)) stepBFS(currDepth + 1, allDepths)
    else allDepths
  }
}
