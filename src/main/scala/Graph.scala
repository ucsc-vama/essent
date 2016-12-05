package essent

import firrtl._
import firrtl.ir._

import essent.Extract._

import collection.mutable.{ArrayBuffer, BitSet, HashMap}
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
  // Vertex name -> corresponding FIRRTL statement
  val nameToStmt = HashMap[String,Statement]()

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

  def addNodeWithDeps(result: String, deps: Seq[String], stmt: Statement) = {
    nameToStmt(result) = stmt
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
        println(nameToStmt(idToName(id)))
        println(id + " "  + inNeigh(id))
      }
    }
  }

  def reorderCommands() = {
    val orderedResults = topologicalSort map idToName
    orderedResults filter {nameToStmt.contains} map nameToStmt
  }

  def printTopologyStats() {
    println(s"Nodes: ${nameToStmt.size}")
    println(s"Referenced Nodes: ${idToName.size}")
    val allDegrees = outNeigh map { _.size }
    val totalRefs = allDegrees reduceLeft { _+_ }
    println(s"Total References: $totalRefs")
    val maxDegree = allDegrees reduceLeft { math.max(_,_) }
    val maxDegreeName = idToName(allDegrees.indexOf(maxDegree))
    println(s"Max Degree: $maxDegree ($maxDegreeName)")
    println(s"Approximate Diameter: ${approxDiameter()}")
  }

  def printSinks(extSignals: Seq[String]) {
    val extSet = extSignals.toSet
    val sinkSignals = nameToID filter
      { case (name, id) => !name.endsWith("$next") && !extSet.contains(name)} filter {
        case (name, id) => outNeigh(id).size == 0 }
    println(sinkSignals.size)
  }

  def approxDiameter(numTrials: Int = 64) = {
    val numNodes = nameToID.size
    val maxPaths = (0 until numTrials) map { trialNumber =>
      val source = Random.nextInt(numNodes)
      val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
      startingDepths(source) = 0
      val depths = stepBFS(Seq(source), startingDepths)
      val maxDepth = depths reduceLeft { math.max(_,_) }
      (maxDepth, s"${idToName(source)} -> ${idToName(depths.indexOf(maxDepth))}")
    }
    val longestPath = maxPaths.sortWith {_._1 < _._1 }.last
    println(s"Longest Path Found: ${longestPath._2}")
    longestPath._1
  }

  def stepBFS(frontier: Seq[Int], depths: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    if (frontier.isEmpty) depths
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
        if (depths(neigh) == -1) {
          depths(neigh) = depths(id) + 1
          Seq(neigh)
        } else Seq()
      }}}
      stepBFS(nextFrontier, depths)
    }
  }

  def crawlBack(ids: Seq[Int], dontPass: ArrayBuffer[Boolean], muxNameID: Int) = {
    val q = new scala.collection.mutable.Queue[Int]
    val result = new scala.collection.mutable.ArrayBuffer[Int]
    val marked = new BitSet()
    ids foreach { id =>
      if (!dontPass(id) && (outNeigh(id) forall {
        consumer => marked(consumer) || consumer == muxNameID
      })) {
        result += id
        marked(id) = true
        q ++= inNeigh(id)
      }
    }
    while (!q.isEmpty) {
      val currId = q.dequeue
      if (!dontPass(currId) && !marked(currId)) {
        if (outNeigh(currId) forall ( consumer => marked(consumer) )) {
          marked(currId) = true
          result += currId
          q ++= inNeigh(currId)
        }
      }
    }
    (result.toSeq) filter { id => nameToStmt.contains(idToName(id)) } map idToName
  }

  def grabIDs(e: Expression): Seq[Int] = e match {
    case l: Literal => Seq()
    case w: WRef => if (w.name.contains("[")) Seq() else Seq(nameToID(w.name))
    case p: DoPrim => p.args flatMap grabIDs
    case _ => throw new Exception(s"expression is not a WRef $e")
  }

  def findAllShadows(muxNames: Seq[String], dontPassSigs: Seq[String]) = {
    val dontPass = ArrayBuffer.fill(nameToID.size)(false)
    dontPassSigs foreach {
      name: String => if (nameToID.contains(name)) dontPass(nameToID(name)) = true
    }
    val shadows = muxNames flatMap {name =>
      val muxExpr = grabMux(nameToStmt(name))
      val muxNameID = nameToID(name)
      // FUTURE: check to make sure not equal
      val tShadow = crawlBack(grabIDs(muxExpr.tval), dontPass, muxNameID)
      val fShadow = crawlBack(grabIDs(muxExpr.fval), dontPass, muxNameID)
      Seq((name, tShadow, fShadow))
    }
    shadows
  }

  def growZones(frontier: Seq[Int], zones: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    // println(s"${(zones filter {_ == -1}).size} / ${zones.size}")
    if (frontier.isEmpty) zones
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
        if ((zones(neigh) == -1) && (inNeigh(neigh) forall { nneigh =>
            (zones(nneigh) == zones(id)) || (zones(nneigh) == -2)})) {
          inNeigh(neigh) foreach {
            nneigh => if (zones(nneigh) == -2) zones(nneigh) = zones(id)}
          zones(neigh) = zones(id)
          Seq(neigh)
        } else Seq()
      }}}
      growZones(nextFrontier, zones)
    }
  }

  def mergeZones(zones: ArrayBuffer[Int], regIDsSet: Set[Int]) {
    val fringe = (0 until zones.size) filter { id => (zones(id) == -1) &&
                    (inNeigh(id).forall {
                      neigh => (zones(neigh) != -1) && (zones(neigh) != -2)})
    }
    // FUTURE: maybe want to allow fringe to be -2 descendants
    println(fringe.size)
    val mergesWanted = fringe map {id => inNeigh(id) map {zones(_)}}
    val mergesCleaned = mergesWanted filter { !_.isEmpty }
    val numRegsInZones = (zones.zipWithIndex filter { p: (Int, Int) =>
      regIDsSet.contains(p._2) }).groupBy(_._1).mapValues{_.size}
    if (!mergesCleaned.isEmpty) {
      def mergedSize(mergeReq: Seq[Int]) = (mergeReq map numRegsInZones).sum
      val zonesToMerge = mergesCleaned.reduceLeft{ (p1,p2) =>
        if (mergedSize(p1) < mergedSize(p2)) p1 else p2
      }
      val newSize = zonesToMerge.map{numRegsInZones(_)}.sum
      if (newSize < 10) {
        println(s"Zone sizes ${(zonesToMerge map numRegsInZones).mkString("+")}")
        zonesToMerge foreach {zone => println(idToName(zone)) }
        val renameMap = (zonesToMerge.tail map { (_, zonesToMerge.head) }).toMap
        (0 until zones.size) foreach { id =>
          if (renameMap.contains(zones(id))) zones(id) = renameMap(zones(id))}
        val newFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
        growZones(newFront, zones)
        println(s"distinct: ${zones.distinct.size}")
        mergeZones(zones, regIDsSet)
      }
    }
  }

  def findZones(regNames: Seq[String]) = {
    val regIDs = regNames flatMap {name =>
      if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    val zones = ArrayBuffer.fill(nameToID.size)(-1)
    regIDs foreach { id => zones(id) = id }
    (0 until zones.size) foreach {
      id => if ((zones(id) == -1) && (inNeigh(id).size == 0) &&
                nameToStmt.contains(idToName(id)))
                  zones(id) = -2
    }
    growZones(regIDs, zones)
    mergeZones(zones, regIDsSet)
    val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 && p._1 != -2}
    val skipSelf = skipUnreached filter { p => p._1 != p._2 }
    val zonesGrouped = skipSelf groupBy { _._1 }
    val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
    val useNames = zoneMap map { case (k,v) => (idToName(k), v map idToName) }
    useNames
  }
}
