package essent

import firrtl._
import firrtl.ir._

import essent.Extract._

import collection.mutable.{ArrayBuffer, BitSet, HashMap, HashSet}
import scala.util.Random

import scala.io.Source
import scala.math.Ordering.Implicits._
import scala.sys.process._
import java.io.{File, FileWriter}


class Graph {
  // Vertex name (string of destination variable) -> numeric ID
  val nameToID = HashMap[String,Int]()
  // Numeric vertex ID -> name (string destination variable)
  val idToName = ArrayBuffer[String]()
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // Intended vertices (did vertex ID get called with addNode)
  val validNodes = HashSet[Int]()


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
    val potentiallyNewDestID = getID(result)
    validNodes += potentiallyNewDestID
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
      if (temporaryMarks(vertexID)) {
        println(s"${idToName(vertexID)} $vertexID")
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
        println(s"${idToName(id)} $id")
        println(s"  ${inNeigh(id)}")
        println(s"  ${outNeigh(id)}")
      }
    }
  }

  def printNode(nodeName: String) {
    val nodeID = nameToID(nodeName)
    println(s"$nodeName ($nodeID)")
    println(s"  ${inNeigh(nodeID)}")
    println(s"  ${outNeigh(nodeID)}")
  }

  def reorderNames() = {
    topologicalSort filter { validNodes.contains(_) } map idToName
  }

  def numNodes() = validNodes.size

  def numNodeRefs() = idToName.size

  def allOutDegrees() = outNeigh map { _.size }

  def numEdges() = allOutDegrees() reduceLeft { _+_ }

  def printTopologyStats() {
    println(s"Nodes: ${numNodes()}")
    println(s"Referenced Nodes: ${numNodeRefs()}")
    println(s"Total References: ${numEdges()}")
    val allDegrees = allOutDegrees()
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
    (result.toSeq) filter { id => validNodes.contains(id) } map idToName
  }

  def grabIDs(e: Expression): Seq[Int] = e match {
    case l: Literal => Seq()
    case w: WRef => if (w.name.contains("[")) Seq() else Seq(nameToID(w.name))
    case p: DoPrim => p.args flatMap grabIDs
    case _ => throw new Exception(s"expression is not a WRef $e")
  }

  def findAllShadows(muxMap: Map[String,Mux], dontPassSigs: Seq[String]) = {
    val dontPass = ArrayBuffer.fill(nameToID.size)(false)
    dontPassSigs foreach {
      name: String => if (nameToID.contains(name)) dontPass(nameToID(name)) = true
    }
    val shadows = muxMap.keys flatMap {name =>
      val muxExpr = muxMap(name)
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
      val nextFrontier = frontier flatMap { id =>
        outNeigh(id) flatMap { neigh => {
          if ((zones(neigh) == -1) && (inNeigh(neigh) forall { nneigh =>
                  (zones(nneigh) == zones(id)) || (zones(nneigh) == -2)})) {
            // inNeigh(neigh) foreach {
            //   nneigh => if (zones(nneigh) == -2) zones(nneigh) = zones(id)}
            zones(neigh) = zones(id)
            Seq(neigh)
          } else Seq()
      }}}
      growZones(nextFrontier, zones)
    }
  }

  def mergeZones(zones: ArrayBuffer[Int], regIDsSet: Set[Int]) {
    val cutoff = 10
    // warning, cutoff set manually in Compiler.scala
    val fringe = (0 until zones.size) filter { id => (zones(id) == -1) &&
                    (inNeigh(id).forall {
                      neigh => (zones(neigh) != -1) && (zones(neigh) != -2)})
    }
    // FUTURE: maybe want to allow fringe to be -2 descendants
    println(fringe.size)
    val mergesWanted = fringe map {id => inNeigh(id).map(zones(_)).distinct}
    val mergesCleaned = mergesWanted filter { !_.isEmpty }
    val numRegsInZones = (zones.zipWithIndex filter { p: (Int, Int) =>
      regIDsSet.contains(p._2) }).groupBy(_._1).mapValues{_.size}
    if (!mergesCleaned.isEmpty) {
      def mergedSize(mergeReq: Seq[Int]) = (mergeReq map numRegsInZones).sum
      val zonesToMerge = mergesCleaned.reduceLeft{ (p1,p2) =>
        if (mergedSize(p1) < mergedSize(p2)) p1 else p2
      }
      val newSize = zonesToMerge.map{numRegsInZones(_)}.sum
      if (newSize < cutoff) {
        println(s"Zone sizes ${(zonesToMerge map numRegsInZones).mkString("+")}")
        zonesToMerge foreach {zone => println(idToName(zone)) }
        val renameMap = (zonesToMerge.tail map { (_, zonesToMerge.head) }).toMap
        (0 until zones.size) foreach { id =>
          if (renameMap.contains(zones(id))) zones(id) = renameMap(zones(id))}
        val newFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
        growZones(newFront, zones)
        val numZones = zones.groupBy(i => i).values.filter(_.size > cutoff).size
        println(s"distinct: $numZones")
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
                validNodes.contains(id))
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

  def mergeZonesML(zones: ArrayBuffer[Int], regIDsSet: Set[Int], frozenZones: Set[Int]) {
    val cutoff = 16
    val fringe = (0 until zones.size) filter { id =>
                    (zones(id) == -1) &&
                    (inNeigh(id) forall { neigh => zones(neigh) != -1 } )
    }
    println(s"Finge size: ${fringe.size}")
    val mergesWanted = fringe map {id => inNeigh(id).map(zones(_)).distinct}
    val mergesCleaned = mergesWanted map {_ filter {_ != -2}} filter { !_.isEmpty } filter { _ forall { !frozenZones.contains(_)}}
    // map from zone ID to seq of member ids
    val zoneMap = zones.zipWithIndex.groupBy(_._1) mapValues { _ map {_._2} }
    // number of zone inputs as signals (registers in future)
    val inDegreeToZone = zoneMap mapValues { zoneMembers =>
      (zoneMembers.flatMap{ inNeigh(_) }.toSeq.distinct diff zoneMembers).size
    }
    if (!mergesCleaned.isEmpty) {
      def mergedSize(mergeReq: Seq[Int]) = (mergeReq map inDegreeToZone).sum
      // using reduce left to find smallest new merged zone
      val zonesToMerge = mergesCleaned.reduceLeft{ (p1,p2) =>
        if (mergedSize(p1) < mergedSize(p2)) p1 else p2
      }
      val newSize = zonesToMerge.map{inDegreeToZone(_)}.sum
      if (newSize < cutoff) {
        println(s"Zone sizes ${(zonesToMerge map inDegreeToZone).mkString("+")}")
        zonesToMerge foreach {zone => println(idToName(zone)) }
        val renameMap = (zonesToMerge.tail map { (_, zonesToMerge.head) }).toMap
        (0 until zones.size) foreach { id =>
          if (renameMap.contains(zones(id))) zones(id) = renameMap(zones(id))}
        val newFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
        growZones(newFront, zones)
        val numZones = zones.groupBy(i => i).values.filter(_.size > cutoff).size
        println(s"distinct: $numZones")
        mergeZonesML(zones, regIDsSet, frozenZones)
      }
    }
  }

  def findZonesML(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val regIDs = regNames flatMap {name =>
    if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val zones = ArrayBuffer.fill(nameToID.size)(-1)
    regIDs foreach { id => zones(id) = id }
    val otherZoneSeeds = (0 until zones.size) filter {
      id => (zones(id) == -1) && (inNeigh(id).size == 0) && !validNodes.contains(id)
    }
    otherZoneSeeds foreach { id => zones(id) = id }
    val sourceZoneSeeds = (0 until zones.size) filter {
      id => (zones(id) == -1) && (inNeigh(id).size == 0) && validNodes.contains(id)
    }
    sourceZoneSeeds foreach { zones(_) = -2 }
    growZones(sourceZoneSeeds, zones)
    val firstFront = (0 until zones.size) filter { id => (zones(id) == -1) && validNodes.contains(id) &&
                      (inNeigh(id).forall { parent => (zones(parent) != -1) })
    }
    firstFront foreach { id => zones(id) = id }
    val startingFront = (0 until zones.size) filter { id => (zones(id) != -1) && (zones(id) != -2) }
    growZones(startingFront, zones)
    mergeZonesML(zones, regIDsSet, regIDsSet)
    (0 until 3) foreach { n => {
      println(s"doing layer $n")
      findZonesMLHelper(zones, regIDsSet)
    }}
    val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 }
    // val skipSelf = skipUnreached filter { p => p._1 != p._2 }
    val zonesGrouped = skipUnreached groupBy { _._1 }
    val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
    // val smallZonesRemoved = zoneMap filter { _._2.size > 10 }
    val smallZonesRemoved = zoneMap filter {
      case (name,members) => !(members filter validNodes).isEmpty
    }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  def findZonesMLHelper(zones: ArrayBuffer[Int], regIDsSet: Set[Int]) {
    val frozenZones = zones.toSet
    val frontier = (0 until zones.size) filter { id => (zones(id) == -1) &&
                      (inNeigh(id).forall { neigh => (zones(neigh) != -1) })
    }
    frontier foreach { id => zones(id) = id }
    growZones(frontier, zones)
    mergeZonesML(zones, regIDsSet, frozenZones)
  }

  // makes zones by evenly splitting output of topo sort
  def findZonesTopo(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val numParts = 1000
    val topoOrder = topologicalSort()
    val partSize = topoOrder.size / numParts
    val intoParts = topoOrder.grouped(partSize).toSeq
    val zoneMap = (intoParts map { l => (l.head, l) }).toMap
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val smallZonesRemoved = zoneMap filter {
      case (name,members) => !(members filter validNodes).isEmpty
    }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  // makes zones by splitting output of topo sort every time a new search is started
  def findZonesTopo2(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val topoOrder = topologicalSort()
    val regIDs = regNames flatMap {name =>
      if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
    regIDs foreach {regID => startingDepths(regID) = 0}
    val depths = stepBFSDepth(regIDsSet, startingDepths)
    val topoSearches = topoOrder.foldLeft((100, Seq[Seq[Int]]())) {
      case ((lastDepth:Int , partList:Seq[Seq[Int]]), id:Int) => {
        if (depths(id) < lastDepth) (depths(id), partList :+ Seq(id))
        else (depths(id), partList.init :+ (partList.last :+ id))
    }}._2
    val zoneMap = (topoSearches map { l => (l.head, l) }).toMap
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val smallZonesRemoved = zoneMap filter {
      case (name,members) => !(members filter validNodes).isEmpty
    }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  // makes zones by splitting output of topo sort every time a new search is started, then clumps them
  def findZonesTopo3(regNames: Seq[String], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val numParts = 1000
    val topoOrder = topologicalSort()
    val partSize = topoOrder.size / numParts
    val regIDs = regNames flatMap {name =>
      if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
    regIDs foreach {regID => startingDepths(regID) = 0}
    val depths = stepBFSDepth(regIDsSet, startingDepths)
    val topoSearches = topoOrder.foldLeft((100, Seq[Seq[Int]]())) {
      case ((lastDepth:Int , partList:Seq[Seq[Int]]), id:Int) => {
        if (depths(id) < lastDepth) (depths(id), partList :+ Seq(id))
        else (depths(id), partList.init :+ (partList.last :+ id))
    }}._2
    val clumped = topoSearches.tail.foldLeft(Seq[Seq[Int]](topoSearches.head)) {
      case (partList:Seq[Seq[Int]], currPart:Seq[Int]) => {
        if (partList.last.size > partSize) partList :+ currPart
        else partList.init :+ (partList.last ++ currPart)
    }}
    val zoneMap = (clumped map { l => (l.head, l) }).toMap
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val smallZonesRemoved = zoneMap filter {
      case (name,members) => !(members filter validNodes).isEmpty
    }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  def partialCutCost(order: Seq[Int], orderInv: Map[Int,Int], currStart: Int,
                     desiredEnd: Int) = {
    val nodesExposed = (currStart until desiredEnd) map order
    val nodeDests = nodesExposed flatMap { id => outNeigh(id) }
    val destsPastEnd = nodeDests map orderInv filter { _ >= desiredEnd }
    destsPastEnd.toSet.size
  }

  def pickBestSplit(order: Seq[Int], orderInv: Map[Int,Int], scoresWithSplits: Seq[(Int,Int)],
                    lastScoreIndex: Int, maxPartSize: Int) = {
    def splitCost(splitAt: Int) = scoresWithSplits(splitAt)._1 +
                    partialCutCost(order, orderInv, splitAt, lastScoreIndex + 1)
    val nodesToConsider = (math.max(0, lastScoreIndex-maxPartSize) to lastScoreIndex)
    val costsWithNodes = nodesToConsider map { id => (splitCost(id), id)}
    def minPair(pA: (Int,Int), pB: (Int,Int)) = {
      if (pA < pB) pA
      else pB
    }
    costsWithNodes.reduceLeft(minPair)
  }

  def kernHelper(order: Seq[Int], orderInv: Map[Int,Int], maxPartSize: Int,
                 scoresWithSplits: Seq[(Int,Int)]): Seq[(Int,Int)] = {
    if (scoresWithSplits.size < order.size) {
      val (lowestScore, splitIndex) = pickBestSplit(order, orderInv,
                                        scoresWithSplits, scoresWithSplits.size - 1, maxPartSize)
      kernHelper(order, orderInv, maxPartSize, scoresWithSplits :+ (lowestScore, splitIndex))
    } else scoresWithSplits
  }

  def pickOutSplits(scoresWithSplits: Seq[(Int,Int)], currIndex: Int): Seq[Int] = {
    val topoID = scoresWithSplits(currIndex)._2
    if (topoID > 0) Seq(topoID) ++ pickOutSplits(scoresWithSplits, topoID)
    else Seq(topoID)
  }

  def splitUpSeq(l: Seq[Int], splits: Seq[Int], offset: Int=0): Seq[Seq[Int]] = {
    val globalIndex = splits.head
    val (part, rest) = l.splitAt(globalIndex - offset)
    if (splits.tail.isEmpty) Seq(part)
    else Seq(part) ++ splitUpSeq(rest, splits.tail, globalIndex)
  }

  // make zones from Kernigan approach after topo sorting graph
  def findZonesKern(regNames: Seq[String], doNotShadow: Seq[String]) = {
    val maxPartSize = 50
    val topoOrder = topologicalSort()
    val getOrderID = topoOrder.zipWithIndex.toMap
    val scoresWithSplits = kernHelper(topoOrder, getOrderID, maxPartSize, Seq((0,topoOrder.size)))
    val splitIndices = pickOutSplits(scoresWithSplits, scoresWithSplits.size-1).reverse
    val intoParts = splitUpSeq(topoOrder, splitIndices) filter { !_.isEmpty }
    val zoneMap = (intoParts map { l => (l.head, l) }).toMap
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val smallZonesRemoved = zoneMap filter {
      case (name,members) => !(members filter validNodes).isEmpty
    }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(validMembers.head) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  def analyzeZoningQuality(zoneMap: Map[String, Graph.ZoneInfo]) {
    println(s"Zones: ${zoneMap.size}")
    val nodesInZones = zoneMap.flatMap(_._2.members).toSet
    val percNodesInZones = 100d * nodesInZones.size / numNodes()
    println(f"Nodes in zones: ${nodesInZones.size} ($percNodesInZones%2.1f%%)")
    // Only counting edges that stay within a zone
    val numEdgesInZones = (zoneMap.values map { case Graph.ZoneInfo(inputs, members, outputs) => {
      val zoneNodeIDs = (members map nameToID).toSet
      (members map nameToID map { nodeID =>
        (outNeigh(nodeID) filter { zoneNodeIDs.contains(_) }).size }).sum
    }}).sum
    val percEdgesInZones = 100d * numEdgesInZones / numEdges()
    println(f"Edges in zones: $numEdgesInZones ($percEdgesInZones%2.1f%%)")
    val numNodesPerZone = nodesInZones.size.toDouble / zoneMap.size
    println(f"Nodes/zone: $numNodesPerZone%.1f")
    val numInputsPerZone = (zoneMap.values map { _.inputs.size }).sum.toDouble / zoneMap.size
    println(f"Inputs/zone: $numInputsPerZone%.1f")
  }

  def stepBFSZone(frontier: Set[Int], sources: ArrayBuffer[Set[Int]]): ArrayBuffer[Set[Int]] = {
    if (frontier.isEmpty) sources
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
        sources(neigh) ++= sources(id)
        Seq(neigh)
      }}}
      stepBFSZone(nextFrontier.toSet, sources)
    }
  }

  def stepBFSDepth(frontier: Set[Int], depths: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    if (frontier.isEmpty) depths
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
        if (depths(neigh) == -1) {
          depths(neigh) = depths(id) + 1
          Seq(neigh)
        } else {
          Seq()
        }
      }}}
      stepBFSDepth(nextFrontier.toSet, depths)
    }
  }

  def stepBFSDepthMax(frontier: Set[Int], depths: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    if (frontier.isEmpty) depths
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
        if (depths(id) + 1 > depths(neigh)) {
          depths(neigh) = depths(id) + 1
          Seq(neigh)
        } else {
          Seq()
        }
      }}}
      stepBFSDepthMax(nextFrontier.toSet, depths)
    }
  }

  // computes all source vertices that are ancestors (not quite full transitive closure)
  def stepBFSSources(frontier: Set[Int], sources: ArrayBuffer[Set[Int]]): ArrayBuffer[Set[Int]] = {
    if (frontier.isEmpty) sources
    else {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh => {
          sources(neigh) ++= sources(id)
          Seq(neigh)
      }}}
      stepBFSSources(nextFrontier.toSet, sources)
    }
  }

  def zoneConsumers(nodesInZone: Seq[Int]): Seq[Int] = {
    nodesInZone.flatMap(outNeigh(_)).distinct diff nodesInZone
  }

  def zoneInputs(nodesInZone: Seq[Int]): Seq[Int] = {
    nodesInZone.flatMap(inNeigh(_)).distinct diff nodesInZone
  }

  def zoneOutputs(nodesInZone: Seq[Int]): Seq[Int] = {
    val nodesInZoneSet = nodesInZone.toSet
    nodesInZone filter { nodeID => outNeigh(nodeID) exists {
      neigh => !nodesInZoneSet.contains(neigh)
    }}
  }

  def findZoneMembers(zoneID: Int, zones: ArrayBuffer[Int]) = {
    zones.zipWithIndex.filter(_._1 == zoneID).map(_._2).toSeq
  }

  def findCoParents(regId: Int, grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
    grouped.keys.filter(_.contains(regId)).reduceLeft(_ ++ _)
  }

  def findNumKids(regSet: Set[Int], grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
    grouped.filter{
      case (k,v) => k.intersect(regSet).size == regSet.size
    }.values.map(_.size).sum
  }

  def writeCOOFile(filename: String, order: Option[Seq[String]] = None) {
    val intOrder = if (order.isEmpty) List.range(0, outNeigh.size)
                   else (order.get map nameToID)
    val renameMap = intOrder.zipWithIndex.toMap
    val fw = new FileWriter(new File(filename))
    validNodes foreach { rowID => {
      outNeigh(rowID) foreach { colID => {
        fw.write(s"${renameMap(rowID)} ${renameMap(colID)} 1\n")
      }}
    }}
    fw.close()
  }

  def writeDotFile(filename: String) {
    val fw = new FileWriter(new File(filename))
    fw.write("digraph rocketchip {\n")
      // (0 until numNodeRefs())
    validNodes foreach { rowID => {
      outNeigh(rowID) foreach { colID => {
        fw.write(s"  ${idToName(rowID)} -> ${idToName(colID)};\n")
      }}
    }}
    fw.write("}\n")
    fw.close()
  }

  def writeMetisFile(filename: String) {
    val fw = new FileWriter(new File(filename))
    fw.write(s"${numNodeRefs()} ${numEdges()} 000\n")
    (0 until numNodeRefs()) foreach { rowID => {
      val neighs = (outNeigh(rowID) ++ inNeigh(rowID)).distinct map { _ + 1 }
      fw.write(s"${neighs.mkString(" ")}\n")
    }}
    fw.close()
  }

  def baseSigName(sigName: String): String = {
    val lastUnderscoreIndex = sigName.lastIndexOf('_')
    if ((lastUnderscoreIndex == -1) || (lastUnderscoreIndex == (sigName.size-1)))
      sigName
    else {
      val suffix = sigName.slice(lastUnderscoreIndex+1, sigName.size)
      if ((sigName(lastUnderscoreIndex-1) == 'T') || (suffix.contains('.')) ||
          (suffix exists {!_.isDigit}))
        sigName
      else
        sigName.slice(0, lastUnderscoreIndex)
    }
  }

  def writeDegreeFile(regNames: Seq[String], filename: String) {
    val fw = new FileWriter(new File(filename))
    val allSources = (0 until numNodeRefs()) filter { inNeigh(_).isEmpty }
    val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
    allSources foreach {id => startingDepths(id) = 0}
    val depths = stepBFSDepth(allSources.toSet, startingDepths)
    val startingDepthsMax = ArrayBuffer.fill(nameToID.size)(-1)
    allSources foreach {id => startingDepthsMax(id) = 0}
    val maxDepths = stepBFSDepthMax(allSources.toSet, startingDepthsMax)
    val startingSources = ArrayBuffer.fill(nameToID.size)(Set[Int]())
    allSources foreach { id => startingSources(id) += id }
    val ancestorSources = stepBFSSources(allSources.toSet, startingSources)
    val baseSources = (allSources map idToName map baseSigName).distinct
    println(s"Total sources: ${allSources.size}")
    println(s"Total base sources: ${baseSources.size}")
    validNodes foreach { nodeID => {
      val inDegree = inNeigh(nodeID).size
      val outDegree = outNeigh(nodeID).size
      val numSources = ancestorSources(nodeID).size
      fw.write(s"${idToName(nodeID)} $inDegree $outDegree ${depths(nodeID)} ${maxDepths(nodeID)} $numSources\n")
    }}
    fw.close()
  }

  def RCMordering() = {
    // Find depth 0 nodes to seed search
    val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
    val sourceNodes = (0 until inNeigh.size) filter { inNeigh(_).size == 0 }
    sourceNodes foreach {id => startingDepths(id) = 0}
    val depths = stepBFSDepth(sourceNodes.toSet, startingDepths)
    val depth0Nodes = depths.zipWithIndex.collect{ case (d,i) if d == 0 => i}
    // Order initial frontier ascending by degree
    val sortedByOutDegree = sortByOutDegree(depth0Nodes)
    val visited = ArrayBuffer.fill(nameToID.size)(false)
    sortedByOutDegree foreach { visited(_) = true }
    val orderedIDs = RCMstep(sortedByOutDegree, visited).reverse
    orderedIDs filter { validNodes } map idToName
  }

  def sortByOutDegree(nodes: Seq[Int]) = {
    nodes map { id => (id, outNeigh(id).size) } sortBy { _._2 } map { _._1 }
  }

  def RCMstep(frontier: Seq[Int], visited: ArrayBuffer[Boolean]): Seq[Int] = {
    val newFront = frontier flatMap { id => {
      val childrenToAdd = outNeigh(id) filter { !visited(_) }
      val childrenOrdered = sortByOutDegree(childrenToAdd)
      childrenOrdered foreach { visited(_) = true }
      childrenOrdered
    }}
    if (newFront.isEmpty) frontier
    else frontier ++ RCMstep(newFront, visited)
  }

  def doubleOrdering() = {
    val identityOrder = ((0 until outNeigh.size) map identity).toSeq
    doDoubleOrder(identityOrder,5) filter validNodes map idToName
  }

  def doDoubleOrder(initialOrder: Seq[Int], times: Int): Seq[Int] = {
    println(s"$times to go")
    if (times == 0) initialOrder
    else {
      val rowAdj = renameGraph(outNeigh, initialOrder)
      val rowOrder = sortGraph(rowAdj)
      val colAdj = renameGraph(inNeigh, rowOrder)
      val colOrder = sortGraph(colAdj)
      // val newOrder = rowOrder.zipWithIndex.toMap
      // rowOrder.zipWithIndex foreach { case(oldID, newID) => {
      //   if (!outNeigh(oldID).isEmpty)
      //     // println(s"$newID ${outNeigh(oldID).head}")
      //     println(s"$newID ${newOrder(outNeigh(oldID).head)}")
      // }}
      doDoubleOrder(colOrder, times - 1)
    }
  }

  // returns bool if idA's adjacencies are lower than idB
  def nodeOrder(idA: Int, idB: Int, adjMap: Map[Int, Seq[Int]], index: Int=0): Boolean = {
    // FUTURE: contemplate right outcome for running out of neighbors
    if ((adjMap(idA).size <= index) || (adjMap(idB).size <= index))
      (adjMap(idA).size < adjMap(idB).size)
    else if (adjMap(idA)(index) == adjMap(idB)(index))
      nodeOrder(idA, idB, adjMap, index+1)
    else adjMap(idA)(index) < adjMap(idB)(index)
  }

  // sorts the vertex IDs based on adjacencies and returns new order
  def sortGraph(adjMap: Map[Int, Seq[Int]]): Seq[Int] = {
    val nodeIDs = (0 until outNeigh.size).toSeq
    nodeIDs sortWith { (idA:Int, idB:Int) => nodeOrder(idA, idB, adjMap) }
  }

  // returns new adjacency list with renames done and neighbors sorted
  // renames is oldIDs in new order, so seq maps newID -> oldID
  def renameGraph(adjList: ArrayBuffer[ArrayBuffer[Int]], renames: Seq[Int]) = {
    // val renameMap = (renames.zipWithIndex map { _.swap }).toMap
    val renameMap = renames.zipWithIndex.toMap
    val renamedAdjMap = ((0 until outNeigh.size) map { oldID: Int => {
      val neighborsRenamed = adjList(oldID) map renameMap
      (renameMap(oldID), neighborsRenamed.sorted)
    }}).toMap
    renamedAdjMap
  }

  def countChains() {
    val chainNodes = validNodes filter {
      id => (inNeigh(id).size == 1) && (outNeigh(id).size == 1)
    }
    val percChainNodes = 100d * chainNodes.size / numNodes()
    println(f"Chain Nodes: ${chainNodes.size} ($percChainNodes%2.1f%%)")
    // want to find number of distinct chains, basically connected components
    val chainIDs = ArrayBuffer.fill(nameToID.size)(-1)
    chainNodes foreach { id => chainIDs(id) = id }
    val finalChainAssignments = countChainsHelper(chainNodes.toSeq, chainIDs)
    val reachedChains = finalChainAssignments filter { _ != -1 }
    val chainGroups = reachedChains groupBy { id => id }
    println(s"# Chains: ${chainGroups.size}")
  }

  def countChainsHelper(frontier: Seq[Int], chainIDs: ArrayBuffer[Int]):ArrayBuffer[Int]  = {
    val newFront = frontier flatMap { id => {
      val parent = inNeigh(id).head
      val child = outNeigh(id).head
      if ((chainIDs(parent) <= chainIDs(id)) && (chainIDs(child) <= chainIDs(id)))
        Seq()
      else {
        if (chainIDs(parent) > chainIDs(id)) chainIDs(parent) = chainIDs(id)
        if (chainIDs(child) > chainIDs(id)) chainIDs(child) = chainIDs(id)
        Seq(id)
      }
    }}
    if (newFront.isEmpty) chainIDs
    else countChainsHelper(newFront, chainIDs)
  }

  def writeHmetisFile(filename: String, regIDs: Seq[Int],
                      grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
    // compressing out empty vertices from ID range, and starting at 1
    val remappedIDs = regIDs.zipWithIndex.toMap.mapValues(_ + 1)
    val fw = new FileWriter(new File(filename))
    fw.write(s"${remappedIDs.size} ${grouped.size}\n")
    grouped foreach { case (triggerSet, children) => {
      val triggersRemapped = triggerSet.toSeq.map(remappedIDs(_))
      fw.write(s"""${children.size} ${triggersRemapped.mkString(" ")}\n""")
    }}
    fw.close()
    remappedIDs
  }

  def generateHmetisRegZones(numZones:Int, regIDs: Seq[Int],
                      grouped: Map[Set[Int],ArrayBuffer[Int]]) = {
    // build input for hmetis
    val filename = "regfile.hm"
    val remappedIDs = writeHmetisFile(filename, regIDs, grouped)
    val metisPath = "/Users/sbeamer/Downloads/hmetis-1.5-osx-i686/shmetis"
    val ubFactor = 10
    // run hmetis
    s"$metisPath regfile.hm $numZones $ubFactor".!
    // parse hmetis output
    val newPartIDs = Source.fromFile(s"$filename.part.$numZones").getLines.toList
    // undo vertex ID remapping and clump register sets
    val unmapIDs = remappedIDs.map(_.swap)
    val partRegIDPairs = newPartIDs zip ((1 to regIDs.size) map { unmapIDs(_) })
    val regGroups = partRegIDPairs.groupBy(_._1).mapValues(_.map(_._2)).values
    // regGroups foreach {
    //   group => println("\n" + group.map(idToName(_)).mkString(","))
    // }
    regGroups
  }

  def findZonesHmetis(regNames: Seq[String]) = {
    val regIDs = regNames flatMap {name =>
      if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    // for all registers, perform BFS and mark reachable (could do in parallel)
    val startingSources = ArrayBuffer.fill(nameToID.size)(Set[Int]())
    regIDs foreach {regID => startingSources(regID) = Set(regID)}
    val finalSources = stepBFSZone(regIDsSet, startingSources)
    // set of inputs -> contained nodes
    val grouped = finalSources.zipWithIndex.groupBy(_._1).mapValues(_.map(_._2))
    val startingRegGroups = generateHmetisRegZones(400, regIDs, grouped)
    val zones = ArrayBuffer.fill(nameToID.size)(-1)
    startingRegGroups foreach { group => {
      val groupID = group.min
      group foreach { regID => zones(regID) = groupID }
    }}
    (0 until zones.size) foreach {
      id => if ((zones(id) == -1) && (inNeigh(id).size == 0) && validNodes.contains(id))
              zones(id) = -2
    }
    growZones(regIDs, zones)
    val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 && p._1 != -2}
    val skipSelf = skipUnreached filter { p => p._1 != p._2 }
    val zonesGrouped = skipSelf groupBy { _._1 }
    val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
    val useNames = zoneMap map { case (k,v) => (idToName(k), v map idToName) }
    useNames
  }

  def scoutZones(regNames: Seq[String]) = {
    val regIDs = regNames flatMap {name =>
      if (nameToID.contains(name)) Seq(nameToID(name)) else Seq()}
    val regIDsSet = regIDs.toSet
    // for all registers, perform BFS and mark reachable (could do in parallel)
    val startingSources = ArrayBuffer.fill(nameToID.size)(Set[Int]())
    regIDs foreach {regID => startingSources(regID) = Set(regID)}
    val finalSources = stepBFSZone(regIDsSet, startingSources)
    // set of inputs -> contained nodes
    val grouped = finalSources.zipWithIndex.groupBy(_._1).mapValues(_.map(_._2))
    // println(grouped)
    // println(regIDs.head)
    // println(idToName(regIDs.head))
    // val coParents = findCoParents(regIDs.head, grouped)
    // println(coParents.size)
    // println(findNumKids(Set(regIDs.head),grouped))
    // val commonRegPrefixes = regNames.groupBy{
    //   s => if (s.contains('_')) s.slice(0,s.lastIndexOf('_')) else s
    // }
    // println(commonRegPrefixes)
    // println(commonRegPrefixes.size)
    // println(regNames.size)
    // println(startingSources.size)
    // println(finalSources.map(_.size).reduceLeft(_ + _))
    // println(grouped.size)
    // finalSources.zipWithIndex.foreach {
    //   case (sources, id) => println(s"${idToName(id)} ${sources.size}")
    // }
    // println(zoneInputs(Seq(34814, 34817, 34948, 34973)))
    // println(zoneOutputs(Seq(34814, 34817, 34948, 34973)))
    // println(finalSources.filter(_.contains(nameToID("dut.T_3641"))).size)
    // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.core.csr.T_5611"))).size)
    // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.icache.s1_pc_"))).size)
    // println(finalSources.filter(_.contains(nameToID("dut.coreplex.DebugModule_1.dbStateReg"))).size)
    // println(finalSources.filter(_.contains(nameToID("dut.coreplex.tileList_0.core.csr.T_5600"))).size)
    // val startingDepths = ArrayBuffer.fill(nameToID.size)(-1)
    // regIDs foreach {regID => startingDepths(regID) = 0}
    // val depths = stepBFSDepth(regIDsSet, startingDepths)
    // val unreachable = depths.zipWithIndex filter { _._1 == -1 } map { _._2 }
    // println(unreachable.size)
    // unreachable foreach { id => println(idToName(id)) }
    // depths.zipWithIndex.foreach {
    //   case (depth, id) => println(s"${idToName(id)} $depth")
    // }
    // println(depths reduceLeft (_ max _))
  }
}

object Graph {
  case class ZoneInfo(inputs: Seq[String], members: Seq[String], outputs: Seq[String])

  def GenReversedChain(n: Int) = {
    val nodeRange = Seq.range(0,n)
    val offset = 1
    val offsetRange = nodeRange.drop(offset) ++ nodeRange.take(offset)
    val edgeList = scala.util.Random.shuffle(nodeRange zip offsetRange)
    val g = new Graph
    edgeList.init foreach { case (idA, idB) => g.addNodeWithDeps("s" + idA, Seq("s" + idB)) }
    g.printTopologyStats()
    g
  }
}
