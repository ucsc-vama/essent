package essent

import essent.Graph.NodeID
import essent.Extract._
import essent.ir._
import firrtl.ir._
import _root_.logger._

import java.io.{File, FileWriter}
import collection.mutable.ArrayBuffer
import scala.collection.{BitSet, mutable}
import scala.reflect.ClassTag







class PreMergeGraph extends StatementGraph {

  val idToPartID = ArrayBuffer[mutable.Set[NodeID]]()
  val partidToID = mutable.HashMap[NodeID, ArrayBuffer[NodeID]]()

  val partInNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()
  val partOutNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()

  val partParentNodes = mutable.HashMap[NodeID, Set[NodeID]]()
  val partChildNodes = mutable.HashMap[NodeID, Set[NodeID]]()

  val partNodeLevel_levelToId = mutable.HashMap[NodeID, ArrayBuffer[ArrayBuffer[NodeID]]]()

  val partNodeLevel_idToLevel = mutable.HashMap[NodeID, mutable.HashMap[NodeID, Int]]()


  def buildFromGraph(sg: StatementGraph): Unit = {
    partInNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
    partOutNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))

    idToPartID.appendAll(ArrayBuffer.fill(sg.numNodes())(mutable.Set[NodeID]()))

    // Deep copy
    outNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
    inNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
    sg.nodeRange foreach { id => {
      sg.outNeigh(id).copyToBuffer(outNeigh(id))
      sg.inNeigh(id).copyToBuffer(inNeigh(id))
    }}

    // Shallow copy (read only)
    nameToID ++= sg.nameToID
    idToName ++= sg.idToName
    idToStmt ++= sg.idToStmt
    validNodes ++= sg.validNodes
//
//    ArrayBuffer.range(0, numNodes()).copyToBuffer(idToMergeID)
//    nodeRange() foreach { id  => mergeIDToMembers(id) = Seq(id) }

  }

  def addNewPartition(nodes: Seq[NodeID]) = {
    if (nodes.isEmpty) throw new Exception("Empty partition")

    val partID = nodes.head

    if (partidToID.contains(partID)) {
      throw new Exception("Partition already exists")
    }

    partidToID(partID) = nodes.to[ArrayBuffer]

    nodes.foreach { nodeID => {
      idToPartID(nodeID) += partID
    }}
  }

  def updatePartConnection() = {
    partInNeigh.clear()
    partOutNeigh.clear()

    partInNeigh.appendAll(ArrayBuffer.fill(numNodes())(ArrayBuffer[NodeID]()))
    partOutNeigh.appendAll(ArrayBuffer.fill(numNodes())(ArrayBuffer[NodeID]()))


    partidToID.keySet.foreach{ pid => {
      val parentNodes = findParentsOutsidePart(pid).toSeq
      val childNodes = findChildsOutsidePart(pid).toSeq

      val parentParts = nodeIDListToPartID(parentNodes)
      val childParts = nodeIDListToPartID(childNodes)

      partParentNodes(pid) = parentNodes.toSet
      partChildNodes(pid) = childNodes.toSet

      partInNeigh(pid) ++= parentParts
      partOutNeigh(pid) ++= childParts
    }}
  }




//  def mergePart(dst: NodeID, src:NodeID): Unit = {
//    // Merge partition src into partition dst
//    val src_nodes = partidToID(src)
//
//    // Fix idToPartID
//    src_nodes.foreach{src_node_id => {
//      idToPartID(src_node_id) -= src
//      idToPartID(src_node_id) += dst
//    } }
//
//    // Fix partidToID
//    partidToID(dst) ++= src_nodes
//    partidToID.remove(src)
//
//    // fix partInNeigh
//    // Remove self link
//    partInNeigh(dst) ++= partInNeigh(src)
//    partInNeigh(dst) -= src
//    partInNeigh(src).clear()
//
//    // fix partOutNeigh
//    partOutNeigh(dst) ++= partOutNeigh(src)
//    partOutNeigh(dst) -= src
//    partOutNeigh(src).clear()
//
//  }

  def findParentsOutsidePart(partID: NodeID) = {
//    (partidToID(partID).flatMap(inNeigh).toSet -- partidToID(partID).flatMap(outNeigh))
    partidToID(partID).flatMap(inNeigh).toSet -- partidToID(partID)
  }

  def findChildsOutsidePart(partID: NodeID) = {
//    (partidToID(partID).flatMap(outNeigh).toSet -- partidToID(partID).flatMap(inNeigh))
    partidToID(partID).flatMap(outNeigh).toSet -- partidToID(partID)
  }

  def nodeIDListToPartID(nodes: Seq[NodeID]) = {
    nodes.flatMap(idToPartID).toSet
  }




//
//  def paintPartConnection(fileName: String) = {
//    val dotWriter = new FileWriter(new File("./", fileName))
//
//    def writeLine(indentLevel: Int, line: String) {
//      dotWriter write ("  "*indentLevel + line + "\n")
//    }
//
//    writeLine(0, "digraph PartConnection {")
//
//    for (eachPart <- partidToID.keySet) {
//      val nodeLabel = s"Part ${eachPart}, Size ${partidToID(eachPart).size}"
//      writeLine(1, s"""n$eachPart [label=\"$nodeLabel\"];""")
//    }
//
//
//    for (eachPart <- partidToID.keySet) {
//      for (eachSrcPart <- partInNeigh(eachPart).distinct) {
//        writeLine(1, s"n$eachSrcPart -> n$eachPart;")
//      }
//    }
//
//    writeLine(0, "}")
//
//    dotWriter.close()
//  }
//


}

object PreMergeGraph {
  def apply(sg: StatementGraph): PreMergeGraph = {
    val pg = new PreMergeGraph
    pg.buildFromGraph(sg)
    pg
  }
}



class PreMerger(pg: PreMergeGraph) extends LazyLogging {


  def findSeeds(smallPartSize: Int = 20) = {
    cutPartReversely()
    getPreMergedSeeds(smallPartSize)
  }

  //  def getPreMergedSeeds(smallPartSize: Int = 20) = {
  //    val collectedParts = _getNonOverlapParts()
  //
  //    val seedToPartID = mutable.HashMap[NodeID, NodeID]()
  //    for (eachPart <- collectedParts) {
  //      seedToPartID(eachPart.head) = eachPart.head
  //    }
  //
  //
  //  }

  def getPreMergedSeeds(smallPartSize: Int) = {
    val seedToPartID = mutable.HashMap[NodeID, NodeID]()
    val partidToSeeds = mutable.HashMap[NodeID, Set[NodeID]]()

    for (eachSeed <- pg.partidToID.keySet) {
      seedToPartID(eachSeed) = eachSeed
      partidToSeeds(eachSeed) = Seq(eachSeed).toSet
    }

    // val partsToMerge = pg.partidToID.keySet.filter{pid => (pg.partidToID(pid).length <= smallPartSize) && pg.partOutNeigh(pid).isEmpty}.toArray

    val partsToMerge = pg.partidToID.keySet.filter{pid => (pg.partidToID(pid).length <= smallPartSize) && pg.partOutNeigh(pid).isEmpty}.toArray

    val partsWithSingleParent = partsToMerge.filter(pg.partInNeigh(_).length <= 1)


//    val smallPartID = pg.partidToID.keySet.filter{pid => {
//      (pg.partidToID(pid).size <= smallPartSize) && (pg.partInNeigh.length <= 1)
//    }}

    partsWithSingleParent.foreach{pid => {
      val toMerge = pg.partInNeigh(pid) ++ Seq(pid)

      // merge those together
      val oldPartIDs = (toMerge map seedToPartID).toSet
      val mergedSeeds = (oldPartIDs flatMap partidToSeeds)
      val newPartID = mergedSeeds.head

      mergedSeeds.foreach{pid => {
        partidToSeeds(pid) = mergedSeeds
        seedToPartID(pid) = newPartID
      }}

    }}

    val validPartIDs = seedToPartID.values.toArray.distinct
    val seeds = validPartIDs map partidToSeeds

//    val seeds_sinkNodeCount = seeds.map(_.size).sum
//
//    println(s"Seeds has $seeds_sinkNodeCount sink nodes, original sinknode count is ${pg.partidToID.size}")

    logger.info(s"Pre-merge: partition number reduced from ${pg.partidToID.size} to ${seeds.size}")

    seeds
  }




  def cutPartReversely(): Unit = {
    val Visited = 1
    val Unvisited = 0
    val Excluded = -1

    val visited = ArrayBuffer.fill(pg.idToName.length)(Unvisited)

    def collectPart(seed: NodeID): Seq[NodeID] = {
      if (visited(seed) != Unvisited) {
        Seq()
      } else {
        visited(seed) = Visited
        pg.idToStmt(seed) match {
          case d: DefRegister => throw new Exception("Shouldnt go here: DefRegister should be set to Excluded")
          // case w: RegUpdate => throw new Exception("Shouldnt go here: RegUpdate cannot be a seed")
          case inv if (!pg.validNodes.contains(seed)) => Seq() // invalid
          case _ => Seq(seed) ++ (pg.inNeigh(seed) flatMap collectPart)
        }
      }
    }


    val allSinkNodes = pg.validNodes.toArray.filter(pg.outNeigh(_).isEmpty)

    pg.idToStmt.zipWithIndex.foreach { case(stmt, id) => {
      stmt match {
        case d: DefRegister => visited(id) = Excluded
        // case ru: RegUpdate => visited(id) = Excluded
        case st if (!pg.validNodes.contains(id)) => visited(id) = Excluded
        case _ => Unit
      }
    }}

    // debug
    logger.info(s"Found ${allSinkNodes.length} sink nodes")

    val collectedParts = (allSinkNodes map collectPart) filter (_.nonEmpty)
    // val partsSorted = collectedParts.sortBy(_.length)(Ordering[Int].reverse)
    
    collectedParts.foreach {part => pg.addNewPartition(part)}
    pg.updatePartConnection()
  }


}


object PreMerger {
  def apply(pg: PreMergeGraph) = {
    new PreMerger(pg)
  }
}