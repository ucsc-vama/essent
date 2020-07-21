package disabled

import firrtl._
import firrtl.ir._

import essent.Util
import essent.Extract._

import collection.mutable.{ArrayBuffer, BitSet, HashMap}
import scala.util.Random

import scala.io.Source
import scala.math.Ordering.Implicits._
import scala.sys.process._
import java.io.{File, FileWriter}


class Graph {

  // Internal data structures
  //----------------------------------------------------------------------------
  // Vertex name (string of destination variable) -> numeric ID
  val nameToID = HashMap[String,Int]()
  // Numeric vertex ID -> name (string destination variable)
  val idToName = ArrayBuffer[String]()
  // numeric vertex ID -> list of incoming vertex IDs (dependencies)
  val inNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // numeric vertex ID -> list outgoing vertex IDs (consumers)
  val outNeigh = ArrayBuffer[ArrayBuffer[Int]]()
  // Intended vertices (did vertex ID get called with addNode)
  val validNodes = BitSet()


  // Graph building
  //----------------------------------------------------------------------------
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

  // automatically filters out duplicates
  def addEdgeIfNew(source: String, dest: String) {
    if (!outNeigh(getID(source)).contains(getID(dest)))
      addEdge(source, dest)
  }

  def addNodeWithDeps(result: String, deps: Seq[String]) = {
    val potentiallyNewDestID = getID(result)
    validNodes += potentiallyNewDestID
    deps foreach {dep : String => addEdge(dep, result)}
  }


  // Stats
  //----------------------------------------------------------------------------
  def numNodes() = validNodes.size

  def numNodeRefs() = idToName.size

  def allOutDegrees() = outNeigh map { _.size }

  def numEdges() = allOutDegrees() reduceLeft { _+_ }

  def nodeRefIDs = 0 until numNodeRefs

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


  // Output
  //----------------------------------------------------------------------------
  // Prints whole graph topology
  override def toString: String = {
    nameToID map {case (longName: String, id: Int) =>
      longName + ": " + inNeigh(id).map{n:Int => idToName(n)}.toSeq.mkString(" ")
    } mkString("\n")
  }

  def printNode(nodeID: Int) {
    println(s"${idToName(nodeID)} ($nodeID)")
    println(s"  ${inNeigh(nodeID).sorted.mkString(" ")}")
    println(s"  ${outNeigh(nodeID).sorted.mkString(" ")}")
  }


  // Topo sort
  //----------------------------------------------------------------------------
  def topologicalSort() = {
    val finalOrdering = ArrayBuffer[Int]()
    val inStack = BitSet()
    val finished = BitSet()
    def visit(vertexID: Int) {
      if (inStack(vertexID)) {
        findCyclesByTopoSort() match {
          case None => throw new Exception("Was a cycle but couldn't reproduce")
          case Some(cycle) => {
            cycle foreach { id => println(idToName(id)) }
            throw new Exception("There is a cycle! (above)")
          }
        }
      } else if (!finished(vertexID)) {
        inStack.add(vertexID)
        inNeigh(vertexID) foreach { neighborID => visit(neighborID) }
        finished.add(vertexID)
        inStack.remove(vertexID)
        finalOrdering += vertexID
      }
    }
    nameToID.values foreach { startingID => visit(startingID) }
    finalOrdering
  }

  def reorderNames() = {
    topologicalSort filter validNodes map idToName
  }

  // FUTURE: remove since findCyclesByTopoSort makes it redundant?
  def topologicalSortWithTracking() = {
    val finalOrdering = ArrayBuffer[Int]()
    val inStack = BitSet()
    val finished = BitSet()
    val callerIDs = ArrayBuffer.fill(nameToID.size)(-1)
    def visit(vertexID: Int, callerID: Int) {
      if (inStack(vertexID)) {
        val cycle = backtrackToFindCycle(callerID, callerIDs, Seq(vertexID))
        cycle foreach printNode
        throw new Exception("There is a cycle!")
      } else if (!finished(vertexID)) {
        if (vertexID != callerID)
          callerIDs(vertexID) = callerID
        inStack.add(vertexID)
        inNeigh(vertexID) foreach { neighborID => visit(neighborID, vertexID) }
        finished.add(vertexID)
        inStack.remove(vertexID)
        finalOrdering += vertexID
      }
    }
    nameToID.values foreach { startingID => visit(startingID, startingID) }
    finalOrdering
  }

  def backtrackToFindCycle(vertexID: Int, callerIDs: ArrayBuffer[Int],
                           cycleSoFar: Seq[Int] = Seq[Int]()): Seq[Int] = {
    if (callerIDs(vertexID) == -1) cycleSoFar
    else if (outNeigh(vertexID).forall(!cycleSoFar.contains(_)))
      backtrackToFindCycle(callerIDs(vertexID), callerIDs, cycleSoFar ++ Seq(vertexID))
    else {
      val loopbackIndices = outNeigh(vertexID) map cycleSoFar.indexOf
      val trimmedCycle = cycleSoFar.drop(loopbackIndices.max)
      trimmedCycle ++ Seq(vertexID)
    }
  }

  def findCyclesByTopoSort(): Option[Seq[Int]] = {
    var cycleFound: Option[Seq[Int]] = None
    val inStack = BitSet()
    val finished = BitSet()
    val callerIDs = ArrayBuffer.fill(nameToID.size)(-1)
    def visit(vertexID: Int, callerID: Int) {
      if (inStack(vertexID)) {
        val cycle = backtrackToFindCycle(callerID, callerIDs, Seq(vertexID))
        cycleFound = Some(cycle)
      } else if (!finished(vertexID)) {
        if (vertexID != callerID)
          callerIDs(vertexID) = callerID
        inStack.add(vertexID)
        inNeigh(vertexID) foreach { neighborID => visit(neighborID, vertexID) }
        finished.add(vertexID)
        inStack.remove(vertexID)
      }
    }
    nameToID.values foreach { startingID => visit(startingID, startingID) }
    cycleFound
  }



  // Mux shadowing
  //----------------------------------------------------------------------------
  def crawlBack(ids: Seq[Int], dontPass: BitSet, muxNameID: Int) = {
    val q = new scala.collection.mutable.Queue[Int]
    val result = new scala.collection.mutable.ArrayBuffer[Int]
    val marked = new BitSet()
    ids foreach { id =>
      if (!dontPass(id) && (outNeigh(id) forall {
        consumer => marked(consumer) || consumer == muxNameID
      })) {
        result += id
        marked.add(id)
        q ++= inNeigh(id)
      }
    }
    while (q.nonEmpty) {
      val currId = q.dequeue
      if (!dontPass(currId) && !marked(currId)) {
        if (outNeigh(currId) forall ( consumer => marked(consumer) )) {
          marked.add(currId)
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
    case m: Mux => Seq(m.cond, m.tval, m.fval) flatMap grabIDs
    case _ => throw new Exception(s"expression is not a WRef $e")
  }

  def findAllShadows(muxMap: Map[String,Mux], dontPassSigs: Seq[String]) = {
    val dontPass = BitSet() ++ dontPassSigs.filter(nameToID.contains).map(nameToID)
    val shadows = muxMap.keys flatMap {name =>
      val muxExpr = muxMap(name)
      val muxNameID = nameToID(name)
      val tShadow = crawlBack(grabIDs(muxExpr.tval), dontPass, muxNameID)
      val fShadow = crawlBack(grabIDs(muxExpr.fval), dontPass, muxNameID)
      Seq((name, tShadow, fShadow))
    }
    shadows
  }


  // Partitioning via MFFCs (for zoning)
  //----------------------------------------------------------------------------
  def initialMFFCs(): ArrayBuffer[Int] = {
    val mffcs = ArrayBuffer.fill(numNodeRefs)(-1)
    nodeRefIDs filterNot validNodes foreach { mffcs(_) = -3 }
    mffcs
  }

  def findMFFCs(priorMFFC: ArrayBuffer[Int] = initialMFFCs()): ArrayBuffer[Int] = {
    val visited = nodeRefIDs filter { id => priorMFFC(id) != -1 && priorMFFC(id) != -3 }
    val fringe = visited flatMap(inNeigh) filter { priorMFFC(_) == -1 }
    val unvisitedSinks = nodeRefIDs filter { id => priorMFFC(id) == -1 && outNeigh(id).isEmpty }
    val newMFFCseeds = unvisitedSinks ++ fringe.distinct
    if (newMFFCseeds.isEmpty) {
      val skipUnreached = priorMFFC filter { mffc => mffc != -1 && mffc != -3 }
      val mffcGrouped = skipUnreached groupBy { identity }
      logger.info(s"# nodes reached: ${skipUnreached.size}")
      logger.info(s"# MFFC's: ${mffcGrouped.size}")
      val biggestSize = mffcGrouped.map{ _._2.size }.max
      logger.info(s"biggest MFFC: $biggestSize")
      priorMFFC
    } else {
      newMFFCseeds foreach { id => priorMFFC(id) = id }
      val mffc = maximizeFFCs(newMFFCseeds, priorMFFC)
      findMFFCs(mffc)
    }
  }

  def maximizeFFCs(fringe: Seq[Int], mffc: ArrayBuffer[Int]): ArrayBuffer[Int] = {
    val fringeAncestors = fringe flatMap inNeigh filter { mffc(_) == -1 }
    val newMembers = fringeAncestors.distinct flatMap { id => {
      val childMFFCs = (outNeigh(id) map mffc).distinct
      if ((childMFFCs.size == 1) && (childMFFCs.head != -1)) {
        mffc(id) = childMFFCs.head
        Seq(id)
      } else Seq()
    }}
    if (newMembers.isEmpty) mffc
    else maximizeFFCs(newMembers, mffc)
  }


  // Cleanups (for zoning)
  //----------------------------------------------------------------------------
  def consolidateSourceZones(zoneMap: Map[Int, Seq[Int]], mffc: ArrayBuffer[Int]): Map[Int, Seq[Int]] = {
    val sourceZones = zoneMap filter { case (k,v) => zoneInputs(v filter validNodes).isEmpty }
    println(s"${sourceZones.size} source MFFCs merged")
    val sourceZoneMembers = sourceZones.values.flatten.toSeq
    sourceZoneMembers foreach { mffc(_) = -2 }
    zoneMap -- sourceZones.keys + (-2 -> sourceZoneMembers)
  }

  def removeDeadZones(zoneMap: Map[Int, Seq[Int]], doNotShadow: Set[Int]): Map[Int, Seq[Int]] = {
    val sinks = nodeRefIDs filter { outNeigh(_).isEmpty }
    val unshadowedSinks = sinks filter {
      sinkID => (!doNotShadow.contains(sinkID)) &&
                (!zoneMap.contains(sinkID) || !zoneMap(sinkID).exists(doNotShadow.contains(_)))
    }
    val deadSinks = (unshadowedSinks filter { !idToName(_).endsWith("$next") }).toSet
    println(s"${deadSinks.size} dead sink MFFCs removed")
    val deadSinkMembers = zoneMap flatMap { case (zoneName, members) => {
      if (deadSinks.contains(zoneName)) members
      else Seq()
    }}
    // FUTURE: set deleted mffc array entries to -1?
    // for now unzone because some seem like legit parents to external IOs
    zoneMap -- deadSinks
  }

  def validInputZones(memberIDs: Seq[Int], zones: ArrayBuffer[Int]) = {
    val inputs = zoneInputs(memberIDs filter validNodes)
    (inputs map zones).distinct filter { _ != -2 }
  }

  def mergeSingleInputMFFCsToParents(zoneMap: Map[Int, Seq[Int]], mffc: ArrayBuffer[Int]): Map[Int, Seq[Int]] = {
    val singleInputZoneMFFCs = zoneMap filter {
      case (name, members) => validInputZones(members, mffc).size == 1
    }
    val singleInputZoneMFFCids = singleInputZoneMFFCs.keys.toSet
    val availSingleInputMFFCs = singleInputZoneMFFCs filter {case (oldZoneID,members) => {
      val newZoneID = validInputZones(members, mffc).head
      !singleInputZoneMFFCids.contains(newZoneID)
    }}
    if (availSingleInputMFFCs.isEmpty) zoneMap
    else {
      println(s"merging in ${availSingleInputMFFCs.size} single-input zones")
      val mergeReqsConsolidated = availSingleInputMFFCs.keys groupBy {
        oldZoneID => {
          val zoneToMergeInto = validInputZones(zoneMap(oldZoneID), mffc).head
          zoneToMergeInto
        }
      }
      val mergeReqs = mergeReqsConsolidated.toSeq map {
        case (parentZone, childZones) => Seq(parentZone) ++ childZones
      }
      val zonesMerged = mergeZonesPar(mergeReqs, zoneMap, mffc)
      mergeSingleInputMFFCsToParents(zonesMerged, mffc)
    }
  }


  // Merging Checks & Stats (for zoning)
  //----------------------------------------------------------------------------
  def safeToMerge(nameA: String, nameB: String): Boolean = {
    val idA = nameToID(nameA)
    val idB = nameToID(nameB)
    !extPathExists(Seq(idA), Seq(idB)) && !extPathExists(Seq(idB), Seq(idA))
  }

  def safeToMergeZones(zoneA: Int, zoneB: Int, zoneMap: Map[Int, Seq[Int]]): Boolean = {
    !extPathExists(zoneMap(zoneA), zoneMap(zoneB)) &&
      !extPathExists(zoneMap(zoneB), zoneMap(zoneA))
  }

  def extPathExists(sourceNodes: Seq[Int], destNodes: Seq[Int]): Boolean = {
    val destNodesSet = destNodes.toSet
    val fringe = zoneOutputs(sourceNodes filter validNodes)
    val exposedFringe = fringe.flatMap(outNeigh).distinct.filter{ !destNodesSet.contains(_) }
    extPathExistsHelper(exposedFringe, BitSet() ++ sourceNodes ++ exposedFringe, destNodesSet)
  }

  def extPathExistsHelper(fringe: Seq[Int], reached: BitSet, destNodes: Set[Int]): Boolean = {
    if (fringe.isEmpty) false
    else {
      val newFringe = fringe flatMap outNeigh filter { !reached(_) }
      if (newFringe exists { destNodes.contains(_)}) true
      else extPathExistsHelper(newFringe.distinct, reached ++ newFringe, destNodes)
    }
  }

  // making sure no external paths exist between any nodes in merge request ids
  def safeToMergeArb(ids: Seq[Int]): Boolean = {
    ids forall { source => !extPathExists(Seq(source), ids diff Seq(source)) }
  }

  // FUTURE: could probably combine helpers
  def pathExists(sourceID: Int, destID: Int): Boolean = {
    pathExistsHelper(Seq(sourceID), BitSet() + sourceID, destID)
  }

  def pathExistsHelper(fringe: Seq[Int], reached: BitSet, destID: Int): Boolean = {
    if (fringe.isEmpty) false
    else {
      val newFringe = (fringe flatMap outNeigh filter { !reached(_) }).distinct
      if (newFringe.contains(destID)) true
      else pathExistsHelper(newFringe, reached ++ newFringe, destID)
    }
  }

  def considerBiggestOverlaps(zoneMap: Map[Int, Seq[Int]]) {
    val zoneToInputs = zoneMap map {
      case (name, members) => (name, zoneInputs(members filter validNodes))
    }
    val allInputZonePairs = zoneToInputs.toSeq flatMap {
      case (name, inputs) => inputs map { (_, name) }
    }
    val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
      case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
    }
    val overlaps = inputToConsumingZones.toSeq map { case (input, consumingZones) => {
      def overlapSize(zoneA: Int, zoneB: Int): Int = {
        zoneToInputs(zoneA).intersect(zoneToInputs(zoneB)).size
      }
      val allCombinations = for (a <- consumingZones; b <- consumingZones) yield (a,b)
      val overlapSizes = allCombinations map { case(a,b) => overlapSize(a,b) }
      // println(s"${idToName(input)} ${overlapSizes.max}")
      (overlapSizes.max, input)
    }}
    val overlapsSorted = overlaps.sorted.reverse
    overlapsSorted foreach { case (size, sigID) => println(s"${idToName(sigID)} $size") }
  }


  // Merging mutations (for zoning)
  //----------------------------------------------------------------------------
  def mergeNodesMutably(nodesToMerge: Seq[String]) {
    val idsToMerge = nodesToMerge map nameToID
    val mergedID = idsToMerge.head
    val idsToRemove = idsToMerge.tail
    val combinedInNeigh = idsToMerge.flatMap(inNeigh(_)).distinct diff idsToMerge
    val combinedOutNeigh = idsToMerge.flatMap(outNeigh(_)).distinct diff idsToMerge
    combinedInNeigh foreach { inNeighID => {
      outNeigh(inNeighID) --= idsToRemove
      if (!outNeigh(inNeighID).contains(mergedID)) outNeigh(inNeighID) += mergedID
    }}
    combinedOutNeigh foreach { outNeighID => {
      inNeigh(outNeighID) --= idsToRemove
      if (!inNeigh(outNeighID).contains(mergedID)) inNeigh(outNeighID) += mergedID
    }}
    inNeigh(mergedID) = combinedInNeigh.to[ArrayBuffer]
    outNeigh(mergedID) = combinedOutNeigh.to[ArrayBuffer]
    idsToRemove foreach { deleteID => {
      inNeigh(deleteID).clear()
      outNeigh(deleteID).clear()
    }}
    if (idsToMerge.exists(validNodes.contains(_)))
      validNodes += mergedID
    validNodes --= idsToRemove
  }

  def disconnectNodes(idA: Int, idB: Int) {
    // println(s"  disconnecting $idA $idB")
    def removeEdge(source: Int, dest: Int) {
      outNeigh(source) = outNeigh(source) filter { _ != dest }
      inNeigh(dest) = inNeigh(dest) filter { _ != source }
    }
    removeEdge(idA, idB)
    removeEdge(idB, idA)
  }

  def mergeZonesPar(mergeReqs: Seq[Seq[Int]], zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int]): Map[Int, Seq[Int]] = {
    val newMergedZones = mergeReqs map { zonesToMerge => {
      val newZoneName = zones(zonesToMerge.head)
      val allMembers = zonesToMerge flatMap zoneMap
      allMembers foreach { zones(_) = newZoneName }
      (newZoneName, allMembers)
    }}
    zoneMap -- mergeReqs.flatten ++ newMergedZones.toMap
  }

  def mergeZonesSafe(mergeReqs: Seq[Seq[Int]], zoneGraph: Graph, zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int]): Map[Int, Seq[Int]] = {
    if (mergeReqs.isEmpty) zoneMap
    else {
      val zonesToMerge = mergeReqs.head
      if (zonesToMerge.size < 2) println("tiny merge req!")
      val zonesStillExist = zonesToMerge.forall{ zoneMap.contains(_) }
      if (!zonesStillExist) {
        // println(s"zones missing ${zonesToMerge}")
        mergeZonesSafe(mergeReqs.tail, zoneGraph, zoneMap, zones)
      } else {
        val allPairs = zonesToMerge.combinations(2).toSeq
        val mergeOK = allPairs.forall{ case Seq(zoneA, zoneB) => zoneGraph.safeToMerge(idToName(zoneA), idToName(zoneB)) }
        if (mergeOK) {
          zoneGraph.mergeNodesMutably(zonesToMerge map idToName)
          val newZoneName = zones(zonesToMerge.head)
          val allMembers = zonesToMerge flatMap zoneMap
          allMembers foreach { zones(_) = newZoneName }
          val newZoneMap = zoneMap -- zonesToMerge + (newZoneName -> allMembers)
          // println(s"ok with ${zonesToMerge}")
          mergeZonesSafe(mergeReqs.tail, zoneGraph, newZoneMap, zones)
        } else {
          // println(s"dropped merge req ${zonesToMerge}")
          mergeZonesSafe(mergeReqs.tail, zoneGraph, zoneMap, zones)
        }
      }
    }
  }

  def mergeIdentInps(zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int]): Map[Int, Seq[Int]] = {
    val zoneToInputs = zoneMap map {
      case (name, members) => (name, zoneInputs(members filter validNodes))
    }
    val allInputZonePairs = zoneToInputs.toSeq flatMap {
      case (name, inputs) => inputs map { (_, name) }
    }
    val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
      case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
    }
    def overlapSize(zoneA: Int, zoneB: Int): Int = {
      zoneToInputs(zoneA).intersect(zoneToInputs(zoneB)).size
    }
    val mergesToConsider = zoneMap.keys flatMap { zoneID => {
      val numInputs = zoneToInputs(zoneID).size.toDouble
      val siblings = (zoneToInputs(zoneID) flatMap inputToConsumingZones filter { _ != zoneID}).distinct
      val fullOverlaps = siblings filter { sibID => overlapSize(zoneID, sibID) == numInputs}
      if (fullOverlaps.isEmpty) Seq()
      else Seq(fullOverlaps :+ zoneID)
    }}
    println(s"Merges for identical inputs: ${mergesToConsider.size}")
    mergeZonesSafe(mergesToConsider.toSeq, buildZoneGraph(zoneMap, zones), zoneMap, zones)
  }

  // merges small zones (<10 members) with other small zones if they share inputs
  def mergeSmallZones(zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int]) = {
    val smallZoneCutoff = 10
    val smallZoneIDs = (zoneMap filter { _._2.size < smallZoneCutoff }).keys.toSet
    val zoneToInputs = zoneMap map {
      case (name, members) => (name, zoneInputs(members filter validNodes))
    }
    val allInputZonePairs = zoneToInputs.toSeq flatMap {
      case (name, inputs) => inputs map { (_, name) }
    }
    val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
      case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
    }
    val inputsToMerge = smallZoneIDs flatMap { smallZoneID => {
      zoneToInputs(smallZoneID) filter {
        inputID => inputToConsumingZones(inputID).forall(smallZoneIDs.contains(_))
      }
    }}
    println(s"${inputsToMerge.size} inputs considered")
    val safeInputsToMerge = inputsToMerge filter { inputID => {
      val siblingsToMerge = inputToConsumingZones(inputID)
      if (siblingsToMerge.size > 1) {
        val allPairs = siblingsToMerge.combinations(2).toSeq
        allPairs.forall{ case Seq(zoneA, zoneB) => safeToMergeZones(zoneA, zoneB, zoneMap) }
      } else false
    }}
    println(s"${safeInputsToMerge.size} inputs safe")
    // score merges
    val inputsScored = safeInputsToMerge map { inputID => {
      val siblingsToMerge = inputToConsumingZones(inputID)
      val allInputChecks = siblingsToMerge flatMap zoneToInputs
      val inputChecksSaved = allInputChecks.size - allInputChecks.distinct.size
      (inputChecksSaved, inputID)
    }}
    // sort by score
    val inputScoresSorted = inputsScored.toSeq.sorted.reverse
    // inputScoresSorted foreach { case (score, inputID) => println(s"${idToName(inputID)} $score")}
    // select valid cover
    val (zonesToBeMerged, takenInputPairs) = inputScoresSorted.foldLeft((Set[Int](), Seq[(Int,Int)]())){
      case ((zonesTaken, scorePairsTaken), (score, inputID)) => {
        val siblingsToMerge = inputToConsumingZones(inputID)
        if (siblingsToMerge.exists(zonesTaken.contains(_)))
          (zonesTaken, scorePairsTaken)
        else {
          (zonesTaken ++ siblingsToMerge.toSet, scorePairsTaken :+ (score, inputID))
        }
      }
    }
    println(s"${takenInputPairs.size} non-conflicting merges")
    println(s"will delete ${takenInputPairs.map(_._1).sum} input checks")
    // perform merges
    val totalZonesToMerge = takenInputPairs.map(_._2).map(inputToConsumingZones(_).size).sum
    println(s"will be merging $totalZonesToMerge zones")
    val mergeReqs = takenInputPairs map { case (score, inputID) => inputToConsumingZones(inputID) }
    mergeZonesSafe(mergeReqs, buildZoneGraph(zoneMap, zones), zoneMap, zones)
    // FUTURE: perform all safety filtering sequentially
    // FUTURE: grow new merges up (fix cycle?)
  }

  // attempts to merge small zones into neighbors, no matter the size
  def mergeSmallZones2(zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int], smallZoneCutoff: Int = 20, mergeThreshold: Double = 0.5): Map[Int, Seq[Int]] = {
    val smallZoneIDs = (zoneMap filter { _._2.size < smallZoneCutoff }).keys.toSet
    println(s"Small zones remaining: ${smallZoneIDs.size}")
    val zoneToInputs = zoneMap map {
      case (name, members) => (name, zoneInputs(members filter validNodes))
    }
    val allInputZonePairs = zoneToInputs.toSeq flatMap {
      case (name, inputs) => inputs map { (_, name) }
    }
    val inputToConsumingZones = allInputZonePairs.groupBy(_._1).map {
      case (input, inputZonePairs) => (input, inputZonePairs.map(_._2))
    }
    def overlapSize(zoneA: Int, zoneB: Int): Int = {
      zoneToInputs(zoneA).intersect(zoneToInputs(zoneB)).size
    }
    val zoneGraph = buildZoneGraph(zoneMap, zones)
    val mergesToConsider = smallZoneIDs flatMap { zoneID => {
      val numInputs = zoneToInputs(zoneID).size.toDouble
      val siblings = (zoneToInputs(zoneID) flatMap inputToConsumingZones filter { _ != zoneID}).distinct
      val sibsScored = siblings map {
        sibID => (overlapSize(zoneID, sibID) / numInputs, sibID)
      }
      val choices = sibsScored filter { _._1 >= mergeThreshold }
      val topChoice = choices.find {
        case (score, sibID) => zoneGraph.safeToMerge(idToName(sibID), idToName(zoneID))
      }
      if (topChoice.isEmpty) Seq()
      else Seq(Seq(topChoice.get._2, zoneID))
    }}
    println(s"Worthwhile merges: ${mergesToConsider.size}")
    if (mergesToConsider.isEmpty) zoneMap
    else {
      val newZoneMap = mergeZonesSafe(mergesToConsider.toSeq, zoneGraph, zoneMap, zones)
      mergeSmallZones2(newZoneMap, zones)
    }
  }


  // Zoning (MFFC based)
  //----------------------------------------------------------------------------
  def findZonesMFFC(doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val mffc = findMFFCs()
    val zoneMapWithSources = Util.groupIndicesByValue(mffc)
    val zoneMap = zoneMapWithSources - (-2)
    val sourceZonesConsolidated = consolidateSourceZones(zoneMap, mffc)
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    val noDeadMFFCs = removeDeadZones(sourceZonesConsolidated, doNotShadowSet)
    val singlesMergedUp = mergeSingleInputMFFCsToParents(noDeadMFFCs, mffc)
    val smallZonesMerged = mergeSmallZones(singlesMergedUp, mffc)
    val smallZonesMerged2 = mergeSmallZones2(smallZonesMerged, mffc)
    val smallZonesMerged3 = mergeSmallZones2(smallZonesMerged2, mffc, 40, 0.25)
    smallZonesMerged3 map { case (zoneID, zoneMemberIDs) => {
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(zoneID) else "ZONE_SOURCE"
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  def buildZoneGraph(zoneMap: Map[Int, Seq[Int]], zones: ArrayBuffer[Int]) = {
    val zoneGraph = new Graph
    zoneMap foreach { case (zoneID, memberIDs) => {
      if (zoneID != -2) {
        val zoneName = idToName(zoneID)
        val inputZones = validInputZones(memberIDs, zones) filter { _ != zoneID }
        val inputNames = inputZones map idToName
        zoneGraph.addNodeWithDeps(zoneName, inputNames)
      }
    }}
    zoneGraph
  }

  def remakeZoneMap(zoneMap: Map[String, Graph.ZoneInfo], doNotShadow: Seq[String]): Map[String, Graph.ZoneInfo] = {
    val doNotShadowSet = (doNotShadow filter {nameToID.contains} map nameToID).toSet
    zoneMap map { case (zoneName, Graph.ZoneInfo(_, givenMembers, _)) => {
      val zoneMemberIDs = givenMembers map nameToID
      val validMembers = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(validMembers) map idToName
      val memberNames = validMembers map idToName
      val outputNames = (zoneOutputs(validMembers) ++ (doNotShadowSet.intersect(validMembers.toSet))).distinct map idToName
      (zoneName, Graph.ZoneInfo(inputNames, memberNames, outputNames))
    }}
  }

  def writeZoneInfo(filename: String, zoneMap: Map[String, Graph.ZoneInfo]) {
    val fw = new FileWriter(new File(filename))
    zoneMap foreach {
      case (zoneName, Graph.ZoneInfo(inputs, members, outputs)) =>
      fw.write(s"$zoneName ${inputs.size} ${members.size} ${outputs.size}\n")
    }
    fw.close()
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
    val sizeOneZones = zoneMap filter {
      case (name, Graph.ZoneInfo(inputs, members, outputs)) => members.size == 1
    }
    println(s"Number of size 1 zones: ${sizeOneZones.size}")
    val sizeOneDead = sizeOneZones filter {
      case (name, Graph.ZoneInfo(inputs, members, outputs)) => outputs.isEmpty
    }
    println(s"Number of dead size 1 zones: ${sizeOneDead.size}")
    val singleInputZones = zoneMap filter {
      case (name, Graph.ZoneInfo(inputs, members, outputs)) => inputs.size == 1
    }
    println(s"Number of 1 input zones: ${singleInputZones.size}")
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


  // Register merging
  //----------------------------------------------------------------------------
  // Checks that no path from reg writer to any read of that reg
  def safeToMergeReg(regName: String): Boolean = {
    val regID = nameToID(regName)
    val regWriteID = nameToID(regName + "$next")
    val regReaders = outNeigh(regID) filter { _ != regWriteID }
    regReaders forall { readerID => !pathExists(regWriteID, readerID) }
  }

  def findMergeableRegs(regNames: Seq[String]): Seq[String] = {
    val includedRegWrites = regNames filter {
      regName => nameToID.contains(regName) && nameToID.contains(regName + "$next")
    }
    println(s"${includedRegWrites.size}/${regNames.size} registers have zone for $$next")
    val safeToMergeRegs = includedRegWrites filter safeToMergeReg
    println(s"${safeToMergeRegs.size} registers pass individual merge tests")
    // NOTE: still an overestimate since testing safety individually
    safeToMergeRegs
  }

  // Returns successfully merged regs
  def mergeRegsSafe(regNames: Seq[String]): Seq[String] = {
    if (regNames.nonEmpty) {
      val mergeableRegs = findMergeableRegs(regNames)
      val mergedRegs = mergeableRegs flatMap { regNameToMerge => {
        val regIDToMerge = nameToID(regNameToMerge)
        if (safeToMergeReg(regNameToMerge)) {
          val regWriteName = regNameToMerge + "$next"
          val regReaders = outNeigh(regIDToMerge) map idToName filter { _ != regWriteName }
          regReaders foreach { readerName => {
            if (!outNeigh(nameToID(readerName)).contains(nameToID(regWriteName)))
              addEdge(readerName, regWriteName)
          }}
          Seq(regNameToMerge)
        } else {
          println(s"couldn't merge reg $regNameToMerge")
          Seq()
        }
      }}
      println(s"Was able to merge ${mergedRegs.size}/${mergeableRegs.size} of mergeable regs")
      mergedRegs
    } else Seq()
  }


  // Unused traversals and scans
  //----------------------------------------------------------------------------
  def dupeEdgesExist(): Boolean = {
    def dupesInArr(arr: ArrayBuffer[Int]) = arr.size != arr.distinct.size
    nodeRefIDs exists { id => dupesInArr(inNeigh(id)) || dupesInArr(outNeigh(id)) }
  }

  def selfLoopsExist(): Boolean = {
    def selfInArr(self: Int, arr: ArrayBuffer[Int]) = arr.contains(self)
    nodeRefIDs exists { id => selfInArr(id, inNeigh(id)) || selfInArr(id, outNeigh(id)) }
  }

  def findStateDepths(stateElemNames: Seq[String], extIONames: Seq[String]): ArrayBuffer[Int] = {
    val stateLoopbacks = (stateElemNames filter { name => nameToID.contains(name) } map {
      name => (nameToID(name + "$next"), nameToID(name))
    }).toMap
    val stateDepths = ArrayBuffer.fill(numNodeRefs)(-1)
    val startingFrontier = (extIONames filter nameToID.contains map nameToID).toSet
    startingFrontier foreach { id => stateDepths(id) = 0 }
    reachAll(startingFrontier, 0, stateDepths)
    traverseStateDepth(0, stateLoopbacks, stateDepths)
    val unreachedNames = stateDepths.zipWithIndex flatMap {
      case (depth, id) => if (depth == -1) Seq(idToName(id)) else Seq()
    }
    val unreachedState = unreachedNames.toSet.intersect(stateElemNames.toSet)
    println(s"State depth traversal couldn't reach ${unreachedNames.size}")
    println(s"${unreachedState.size}/${stateElemNames.size} state elements unreached")
    println(unreachedState)
    stateDepths
  }

  def traverseStateDepth(lastDepth: Int, stateLoopbacks: Map[Int,Int], regDepths: ArrayBuffer[Int]) {
    val lastReached = regDepths.zipWithIndex flatMap {
      case (depth, id) => if (depth == lastDepth) Seq(id) else Seq()
    }
    val lastReachedStateElems = lastReached filter { stateLoopbacks.contains(_) }
    val startingFrontier = (lastReachedStateElems map stateLoopbacks).toSet
    if (startingFrontier.nonEmpty) {
      println(s"starting depth ${lastDepth+1} with ${startingFrontier.size}")
      startingFrontier foreach { id => regDepths(id) = lastDepth+1 }
      reachAll(startingFrontier, lastDepth+1, regDepths)
      traverseStateDepth(lastDepth+1, stateLoopbacks, regDepths)
    }
  }

  def reachAll(frontier: Set[Int], depth: Int, regDepths: ArrayBuffer[Int]) {
    if (frontier.nonEmpty) {
      val nextFrontier = frontier flatMap { id => outNeigh(id) flatMap { neigh =>
        if (regDepths(neigh) == -1) {
          regDepths(neigh) = depth
          Seq(neigh)
        } else Seq()
      }}
      reachAll(nextFrontier.toSet, depth, regDepths)
    }
  }

  def printDeadRegisters(regNames: Seq[String], otherDeps: Seq[String]) {
    val excludedRegs = regNames.filter(!nameToID.contains(_))
    val dnsRegs = regNames.toSet.intersect(otherDeps.toSet)
    val usedOnlyForPrintsAndAsserts = dnsRegs.intersect(excludedRegs.toSet)
    val unusedRegs = excludedRegs.toSet -- usedOnlyForPrintsAndAsserts
    println(s"${excludedRegs.size} registers are not consumed by graph")
    println(s"${usedOnlyForPrintsAndAsserts.size} used for prints & asserts")
    println(s"${unusedRegs.size} are never read or written")
    // FUTURE: find registers part of disconnected parts of the graph
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

  def chainReplacements(): Map[String, String] = {
    val sourceIDs = nodeRefIDs filter { inNeigh(_).isEmpty }
    def reachableIDs(id: Int): Seq[Int] = {
      Seq(id) ++ (outNeigh(id) flatMap reachableIDs)
    }
    val renamePairs = sourceIDs flatMap {
      sourceID => reachableIDs(sourceID) map { childID => (idToName(childID), idToName(sourceID)) }
    }
    renamePairs.toMap
  }


  // Obscure Output & Stats
  //----------------------------------------------------------------------------
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
    nodeRefIDs foreach { rowID => {
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
    val allSources = nodeRefIDs filter { inNeigh(_).isEmpty }
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
}

object Graph {
  case class ZoneInfo(inputs: Seq[String], members: Seq[String], outputs: Seq[String])
}
