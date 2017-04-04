package essent

import firrtl._
import firrtl.ir._

import essent.Extract._

import collection.mutable.{ArrayBuffer, BitSet, HashMap, HashSet}
import scala.util.Random

import scala.io.Source
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
    val numRegsInZones = (zones.zipWithIndex filter { p: (Int, Int) =>
      regIDsSet.contains(p._2) }).groupBy(_._1).mapValues{_.size}
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
    // regIDs foreach { id => zones(id) = id }
    (0 until zones.size) foreach {
      id => if ((zones(id) == -1) && (inNeigh(id).size == 0) && validNodes.contains(id))
              zones(id) = -2
    }
    // make neighbors of registers initial zone set
    (0 until zones.size) foreach { id =>
      if (!inNeigh(id).isEmpty && (inNeigh(id) forall {
        parentID => ((regIDsSet.contains(parentID)) || (zones(parentID) == -2)) && (zones(id) != -2)
      }))
        zones(id) = id
    }
    val startingFront = (0 until zones.size) filter { id => (zones(id) != -1) }
    growZones(startingFront, zones)
    // growZones(regIDs, zones)
    mergeZonesML(zones, regIDsSet, Set())
    println("trying to do second layer")
    val frozenZones = zones.toSet
    val newFront = (0 until zones.size) filter { id => (zones(id) == -1) &&
                      (inNeigh(id).forall {
                      neigh => (zones(neigh) != -1) && (zones(neigh) != -2)})
    }
    newFront foreach { id => zones(id) = id }
    // growZones(newFront, zones)
    // mergeZonesML(zones, regIDsSet, frozenZones)
    // (0 until zones.size) foreach { id => if (zones(id) == -2) println(idToName(id)) }
    val skipUnreached = zones.zipWithIndex filter { p => p._1 != -1 }
    // val skipSelf = skipUnreached filter { p => p._1 != p._2 }
    val zonesGrouped = skipUnreached groupBy { _._1 }
    val zoneMap = zonesGrouped map { case (k,v) => (k, v map { _._2 })}
    val smallZonesRemoved = zoneMap filter { _._2.size > 10 }
    smallZonesRemoved map { case (zoneID, zoneMemberIDs) => {
      val noSources = zoneMemberIDs filter { id => validNodes.contains(id) }
      val inputNames = zoneInputs(zoneMemberIDs) map idToName
      val memberNames = noSources map idToName
      val outputNames = (zoneOutputs(noSources) ++ (doNotShadowSet.intersect(noSources.toSet))).distinct map idToName
      val zoneName = if (zoneID != -2) idToName(zoneID) else "ZONE_SOURCE"
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
}
