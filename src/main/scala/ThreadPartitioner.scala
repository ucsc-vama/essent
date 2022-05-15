package essent

import essent.Util._
import essent.Graph.NodeID
import essent.Extract._
import essent.ir._
import firrtl.ir._
import _root_.logger._

import java.io.{File, FileWriter}
import collection.mutable.ArrayBuffer
import scala.collection.{BitSet, mutable}
import scala.io.Source
import scala.reflect.ClassTag







class PartGraph extends StatementGraph {

  val idToPartID = ArrayBuffer[mutable.Set[NodeID]]()
//  val partidToID = mutable.HashMap[NodeID, ArrayBuffer[NodeID]]()


  var parts = mutable.ArrayBuffer[BitSet]()
  var edgeCount = 0
  // val validParts = mutable.BitSet()

//  val partInNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()
//  val partOutNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()

  // part connection graph, undirected weighted graph
  val partAdjList = ArrayBuffer[ArrayBuffer[NodeID]]()
  val partAdjList_nodup = ArrayBuffer[ArrayBuffer[NodeID]]()
  val edgeWeight = ArrayBuffer[ArrayBuffer[Int]]()




  def buildFromGraph(sg: StatementGraph): Unit = {
//    partInNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
//    partOutNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
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

  }




  def initPartition(seeds: Array[Set[NodeID]]) = {

    val cache = mutable.HashMap[NodeID, BitSet]()

    def collectPart(seed: NodeID): BitSet = {

      idToStmt(seed) match {
        case inv if (!validNodes.contains(seed)) => BitSet() // invalid
        case d: DefRegister => BitSet() // Stop at register read
        case _ => {
          if (cache.contains(seed)) {
            return cache(seed)
          }
          val ret = BitSet(seed) ++ (inNeigh(seed) flatMap collectPart)
          // Save for data may be used again
          if (outNeigh(seed).length > 1)  cache(seed) = ret
          ret
        }
      }
    }

//    val allValidSinkNodes = validNodes.filter(outNeigh(_).isEmpty)

//    println(s"${allValidSinkNodes.size} sink nodes in total")
    val collectedParts = seeds.map{_.map(collectPart).reduce(_ ++ _)}

//    val collectedParts = ((allValidSinkNodes.toArray map collectPart) filter (_.nonEmpty))

    parts.clear()
    parts ++= collectedParts

    parts.indices.foreach{partID => {parts(partID).foreach{ nodeID => {
      idToPartID(nodeID) += partID
    }}}}


  }


  def updateEdgeInfo() = {

    partAdjList.clear()
    partAdjList ++= (ArrayBuffer.fill(parts.length)(ArrayBuffer[NodeID]()))

    partAdjList_nodup.clear()
    partAdjList_nodup ++= (ArrayBuffer.fill(parts.length)(ArrayBuffer[NodeID]()))

    edgeWeight.clear()
    edgeWeight ++= ArrayBuffer.fill(parts.length)(ArrayBuffer.fill(parts.length)(0))

    edgeCount = 0



//    val partL1Nodes = parts map { part => {
//      (part.flatMap(inNeigh).toSet -- part).flatMap(outNeigh) & part
//    }}


    parts.indices.foreach{i => {
      val partsIntersected = (parts(i) flatMap idToPartID)
      partsIntersected.foreach(j => {
        if (i > j) {
           val duplicateNodeCount = (parts(i) & parts(j)).size
//          val duplicateNodeCount = 1

          edgeCount += 1

          partAdjList(i) += j
          partAdjList(j) += i
          edgeWeight(i)(j) = duplicateNodeCount
          edgeWeight(j)(i) = duplicateNodeCount

          partAdjList_nodup(i) += j
        }
      })
    }}


//      for (i <- parts.indices; j <- ((i+1) until parts.length)) {
////      if ((partL1Nodes(i) & partL1Nodes(j)).nonEmpty){
//
//        // val duplicateNodeCount = (parts(i) & parts(j)).size
//      val duplicateNodeCount = (partL1Nodes(i) & partL1Nodes(j)).size
//      if (duplicateNodeCount != 0){
////        if (duplicateNodeCount != 0) {
//        // edge exists
//        edgeCount += 1
//
//        partAdjList(i) += j
//        partAdjList(j) += i
//        edgeWeight(i)(j) = duplicateNodeCount
//        edgeWeight(j)(i) = duplicateNodeCount
//
//        partAdjList_nodup(i) += j
////        }
//
//      }

  }



  def brief() = {
    // print out info
    val part_count = parts.size
    val node_count = validNodes.size
    val part_node_cnt = (parts.map { _.size }).sum

    print(s"$part_count parts in total, with $node_count valid nodes, $part_node_cnt nodes in parts\n")

  }


  def findPartComponents() = {
    // Find all connected components
    val visited = mutable.Set[NodeID]()
    def traverse(seed: NodeID): Seq[NodeID] = {
      if (visited.contains(seed)) {
        Seq()
      } else {
        visited += seed
        Seq(seed) ++ partAdjList(seed).flatMap(traverse)
      }
    }

    val components = ArrayBuffer[Set[NodeID]]()
    var unvisited = parts.indices.toSet

    while (unvisited.nonEmpty) {
      val newComponent = traverse(unvisited.head).toSet
      components += newComponent
      unvisited = unvisited -- visited
    }

    components
  }




  def paintPartConnection(dir: String, fileName: String) = {
    val dotWriter = new FileWriter(new File(dir, fileName))

    def writeLine(indentLevel: Int, line: String) {
      dotWriter write ("  "*indentLevel + line + "\n")
    }

    writeLine(0, "graph PartConnection {")

    for (eachPart <- parts.indices) {
      val nodeLabel = s"Part ${eachPart}, Size ${parts(eachPart).size}"
      writeLine(1, s"""n$eachPart [label=\"$nodeLabel\"];""")
    }

    for (n1 <- partAdjList_nodup.indices) {
      for (n2 <- partAdjList_nodup(n1)) {
        val weight = edgeWeight(n1)(n2)
        writeLine(1, s"n$n1 -- n$n2[weight=$weight];")
      }
    }

    writeLine(0, "}")

    dotWriter.close()
  }


  def writeToMetis(dir:String, fileName: String) = {

    val writer = new FileWriter(new File(dir, fileName))

    def writeLine(numbers: Seq[Any]) {
      writer write (numbers.mkString(" ") + "\n")
    }


//    val stmtReferenceCount = mutable.HashMap[NodeID, Int]()
//    val partWeight = mutable.HashMap[NodeID, Int]()
//
//    idToStmt.indices.foreach {id => {stmtReferenceCount(id) = 0}}
//    parts.indices.foreach{pid => {partWeight(pid) = 0}}
//
//    parts.foreach{_.foreach{id => {stmtReferenceCount(id) += 1}}}
//
//    val max_ref_count = stmtReferenceCount.values.max
//
//    parts.indices.foreach{ pid => {
//      parts(pid).foreach{ id => {
//        // Add 1 to avoid weight of 0
//        partWeight(pid) += (max_ref_count - stmtReferenceCount(id) + 1)
//      }}
//      partWeight(pid) = (partWeight(pid)) / max_ref_count
//    }}
    println(s"Largest part size is ${parts.map(_.size).max}")


    // metis file header
    // weighted graph, weight on both edges and vertices
    writeLine(Seq(s"${parts.length}", edgeCount, "011"))

    for (node <- parts.indices) {
      val edges = partAdjList(node)
      val weights = edges map edgeWeight(node)

       val node_weight = parts(node).size
      // val node_weight = 1
//      val node_weight = partWeight(node)
      // metis requires node id starts from 1
      val line = Seq(node_weight) ++ ((edges map (_+1)) zip weights).flatten{ case (a, b) => Seq(a, b)}

      writeLine(line)
    }

    writer.close()
  }



}

object PartGraph {
  def apply(sg: StatementGraph): PartGraph = {
    val pg = new PartGraph
    pg.buildFromGraph(sg)
    pg
  }
}



class ThreadPartitioner(pg: PartGraph, opt: OptFlags) extends LazyLogging {

  val gpmetis_path = "gpmetis"

//  val gpmetis_path = "/Users/hwang/project/metis-5.1.0/build/Darwin-arm64/programs/gpmetis"
  val gpmetis_input_filename = "parts.metis"
  val absOutputPath: String = if (java.nio.file.Paths.get(opt.outputDir()).isAbsolute) opt.outputDir() else (os.pwd/os.RelPath(opt.outputDir())).toString()

  val parts = ArrayBuffer[BitSet]()
  val parts_read = ArrayBuffer[Set[Int]]()
  val parts_write = ArrayBuffer[Set[Int]]()


  def doOpt(seeds: Array[Set[NodeID]]) = {

    // pg.paint("opt-raw.dot")

    logger.info("Start collect partitions")
    pg.initPartition(seeds)
    logger.info("Done collect partitions")

    logger.info("Start calculate edge connections")

    val startTime = System.currentTimeMillis()

    pg.updateEdgeInfo()

    val endTime = System.currentTimeMillis()
    val elapse = (endTime - startTime)
    logger.info("Done edge connections")
    logger.info(s"Took $elapse ms")


//    pg.mergeOverlappingParts()
//    pg.clearEmptyParts()
//
//    logger.info("Start calculate edge connections")
//    pg.updateEdgeInfo()
//    logger.info("Done edge connections")

    pg.paintPartConnection(absOutputPath, "opt-part-pre-merged.dot")

    pg.writeToMetis(absOutputPath, gpmetis_input_filename)

    val metis_return_file = hiMetis(opt.parallel)

    val partResult = parseMetisResult(metis_return_file)

    val partCount = partResult.max + 1
    parts ++= ArrayBuffer.fill(partCount)(mutable.BitSet())

    partResult.zipWithIndex.foreach{case(partID, nodeID) => {
      parts(partID) ++= pg.parts(nodeID)
    }}

    parts.indices.foreach{pid => {
      println(s"Pid: $pid, part size: ${parts(pid).size}")
    }}

    val totalNodeCount = parts.map(_.size).sum

    println(s"Total node count is ${totalNodeCount}, original statement graph has ${pg.validNodes.size} valid nodes")


    // Check correctness

    val partNodeCount = pg.parts.reduce(_ ++ _).size

    println(s"Total node counts in partitions (deduplicated) is $partNodeCount")

//    pg.brief()
//
//    val components = pg.findPartComponents()
//    print(s"Size: ${components.map(_.size)}\n")

    // val parts_read = partidToID(partID).flatMap(inNeigh).toSet -- partidToID(partID)


    parts.foreach {part => {
      val part_read = part.flatMap(pg.inNeigh).toSet -- part
      val part_write = part.filter(pg.outNeigh(_).isEmpty).toSet

      val part_write_supect = part_write.filter(pg.idToStmt(_) match {
        case r: RegUpdate => false
        case mw: MemWrite => false
        case p: Print => false
        case st: Stop => false
        case _ => true
      })

      val part_write_suspect_stmt = part_write_supect map pg.idToStmt

      val allRegMems = part filter(pg.idToStmt(_) match {
        case r: RegUpdate => true
        case mw: MemWrite => true
        case _ => false
      })

      val regMemInBetween = allRegMems -- part_write
      val regMemInBetween_stmt = regMemInBetween map pg.idToStmt

      parts_read.append(part_read)
      parts_write.append(part_write)

    }}



    logger.info("Done")

  }



  def hiMetis(desiredParts: Int) = {
    val cmd = List(gpmetis_path,
      (os.Path(absOutputPath)/gpmetis_input_filename).toString(),
      desiredParts.toString,
//      "-objtype=vol"
    )

    val r = os.proc(cmd).call(check = false)

    print(r.out.string)

    assert(r.exitCode == 0, s"Return code is not 0, ${r.exitCode} received.")


    (os.Path(absOutputPath)/(gpmetis_input_filename + ".part." + desiredParts.toString)).toString()
  }


  def parseMetisResult(fileName: String) = {

    val partResult = ArrayBuffer[Int]()

    val fileSource = Source.fromFile(fileName)
    fileSource.getLines.foreach{partID => {
      partResult += partID.toInt
    }}

    fileSource.close()

    partResult
  }



}


object ThreadPartitioner {
  def apply(pg: PartGraph, opt: OptFlags) = {
    new ThreadPartitioner(pg, opt)
  }
}