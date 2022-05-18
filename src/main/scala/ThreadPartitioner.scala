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






class PartGraph extends StatementGraph {

  val idToTreeID = ArrayBuffer[mutable.Set[NodeID]]()
//  val partidToID = mutable.HashMap[NodeID, ArrayBuffer[NodeID]]()

  val idToPieceID = ArrayBuffer[NodeID]()

  val sinkNodes = ArrayBuffer[NodeID]()
  var trees = mutable.ArrayBuffer[BitSet]()
  val pieces = mutable.ArrayBuffer[BitSet]()

  var edgeCount = 0
  // val validParts = mutable.BitSet()

//  val partInNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()
//  val partOutNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()

  // part connection graph, undirected weighted graph
//  val partAdjList = ArrayBuffer[ArrayBuffer[NodeID]]()
//  val partAdjList_nodup = ArrayBuffer[ArrayBuffer[NodeID]]()
//  val edgeWeight = ArrayBuffer[ArrayBuffer[Int]]()

  val pieceInNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()
  val pieceOutNeigh = ArrayBuffer[ArrayBuffer[NodeID]]()
  val pieceAdjList_dup = ArrayBuffer[ArrayBuffer[NodeID]]()

  val pieceEdgeWeight = ArrayBuffer[mutable.HashMap[Int, Int]]()



  def buildFromGraph(sg: StatementGraph): Unit = {
//    partInNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
//    partOutNeigh.appendAll(ArrayBuffer.fill(sg.numNodes())(ArrayBuffer[NodeID]()))
    idToTreeID.appendAll(ArrayBuffer.fill(sg.numNodes())(mutable.Set[NodeID]()))
    idToPieceID ++= ArrayBuffer.fill(sg.numNodes())(-1)


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




  def initPartition() = {

    sinkNodes ++= validNodes.filter(outNeigh(_).isEmpty)

    val cache = mutable.HashMap[NodeID, BitSet]()

    def collectTree(seed: NodeID): BitSet = {

      idToStmt(seed) match {
        case inv if (!validNodes.contains(seed)) => BitSet() // invalid
        case d: DefRegister => BitSet() // Stop at register read
        case _ => {
          if (cache.contains(seed)) {
            return cache(seed)
          }
          val ret = BitSet(seed) ++ (inNeigh(seed) flatMap collectTree)
          // Save for data may be used again
          if (outNeigh(seed).length > 1)  cache(seed) = ret
          ret
        }
      }
    }

//    println(s"${allValidSinkNodes.size} sink nodes in total")
    val collectedParts = sinkNodes.map{collectTree}

    println("Trees collected")

//    val collectedParts = ((allValidSinkNodes.toArray map collectPart) filter (_.nonEmpty))

    trees.clear()
    trees ++= collectedParts

    trees.indices.foreach{partID => {trees(partID).foreach{ nodeID => {
      idToTreeID(nodeID) += partID
    }}}}


    // Assuming pieces(pid) is an empty BitSet
    def findPiece(pid: NodeID)(seed: NodeID): Unit = {
      if (idToPieceID(seed) == -1) {
        pieces(pid) += seed
        idToPieceID(seed) = pid
        val connectedVertecies = (inNeigh(seed) ++ outNeigh(seed)).filter(validNodes.contains)
        val samePieceVertecies = connectedVertecies.filter(vid => {idToTreeID(vid) == idToTreeID(seed)})
        samePieceVertecies foreach findPiece(pid)
      }
    }

    // First, collect all pieces for all sink nodes
    sinkNodes.zipWithIndex.foreach{case(sinkNode, pid) => {
      pieces.append(BitSet())
      findPiece(pid)(sinkNode)
    }}

    // Collect pieces for all other nodes
    do {
      val unvisited = idToPieceID.indices.filter(idToPieceID(_) == -1)
      val newPid = pieces.length
      pieces.append(BitSet())
      findPiece(newPid)(unvisited.head)

    } while(idToPieceID.indices.exists(idToPieceID(_) == -1))

  }


  def updateEdgeInfo() = {

    pieceInNeigh.clear()
    pieceInNeigh ++= (ArrayBuffer.fill(pieces.length)(ArrayBuffer[NodeID]()))

    pieceOutNeigh.clear()
    pieceOutNeigh ++= (ArrayBuffer.fill(pieces.length)(ArrayBuffer[NodeID]()))

    pieceAdjList_dup.clear()
    pieceAdjList_dup ++= (ArrayBuffer.fill(pieces.length)(ArrayBuffer[NodeID]()))

    pieceEdgeWeight.clear()
    pieceEdgeWeight ++= ArrayBuffer.fill(pieces.length)(mutable.HashMap[Int, Int]())


    edgeCount = 0


    def findParentsOutsidePiece(pid: NodeID) = pieces(pid).flatMap(inNeigh).toSet -- pieces(pid)

    def findChildsOutsidePiece(pid: NodeID) = pieces(pid).flatMap(outNeigh).toSet -- pieces(pid)

    def idListToPieceID(ids: Set[NodeID]) = ids.map(idToPieceID).toSet


    // Find edges
    pieces.indices.foreach{ pid_i => {
      val pieceParentNodes = findParentsOutsidePiece(pid_i)
      val pieceChildNodes = findChildsOutsidePiece(pid_i)

      val pieceParents = idListToPieceID(pieceParentNodes)
      val pieceChilds = idListToPieceID(pieceChildNodes)

      pieceInNeigh(pid_i) ++= pieceParents
      pieceOutNeigh(pid_i) ++= pieceChilds

      edgeCount += pieceParents.size

    }}


    // Update edge weight
    val pieceDepSize = mutable.HashMap[NodeID, Int]()

    def findDepSize(pid: Int): Int = {
      if (!pieceDepSize.contains(pid)) {
        val depSize = pieces(pid).size + (pieceInNeigh(pid) map findDepSize).sum
        pieceDepSize(pid) = depSize
      }
      pieceDepSize(pid)
    }

    pieces.indices.foreach{pid_i => {
      pieceInNeigh(pid_i).foreach{pid_j => {
        // Edge pid_i -> pid_j

        val weight = findDepSize(pid_i)

        pieceEdgeWeight(pid_i)(pid_j) = findDepSize(pid_i)
        pieceEdgeWeight(pid_j)(pid_i) = findDepSize(pid_i)
      }}
    }}





//    val partL1Nodes = parts map { part => {
//      (part.flatMap(inNeigh).toSet -- part).flatMap(outNeigh) & part
//    }}


//    parts.indices.foreach{i => {
//      val partsIntersected = (parts(i) flatMap idToPartID)
//      partsIntersected.foreach(j => {
//        if (i > j) {
//           val duplicateNodeCount = (parts(i) & parts(j)).size
////          val duplicateNodeCount = 1
//
//          edgeCount += 1
//
//          partAdjList(i) += j
//          partAdjList(j) += i
//          edgeWeight(i)(j) = duplicateNodeCount
//          edgeWeight(j)(i) = duplicateNodeCount
//
//          partAdjList_nodup(i) += j
//        }
//      })
//    }}


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





  def paintPartConnection(dir: String, fileName: String) = {
    val dotWriter = new FileWriter(new File(dir, fileName))

    def writeLine(indentLevel: Int, line: String) {
      dotWriter write ("  "*indentLevel + line + "\n")
    }

    writeLine(0, "digraph PartConnection {")

    for (eachPart <- pieces.indices) {
      val nodeLabel = s"Part ${eachPart}, Size ${pieces(eachPart).size}"
      writeLine(1, s"""n$eachPart [label=\"$nodeLabel\"];""")
    }

    for (n1 <- pieceOutNeigh.indices) {
      for (n2 <- pieceOutNeigh(n1)) {
        val weight = pieceEdgeWeight(n1)(n2)
        writeLine(1, s"n$n1 -> n$n2[weight=$weight];")
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
    println(s"Largest part size is ${pieces.map(_.size).max}")


    // metis file header
    // weighted graph, weight on both edges and vertices
    writeLine(Seq(s"${pieces.length}", edgeCount, "011"))

    for (node <- pieces.indices) {

      val inEdges = pieceInNeigh(node)
      val outEdges = pieceOutNeigh(node)

      val inWeights = inEdges.map(pieceEdgeWeight(_)(node))
      val outWeights = outEdges.map(pieceEdgeWeight(node)(_))

      val edges = inEdges ++ outEdges
      val weights = inWeights ++ outWeights

       val node_weight = pieces(node).size
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


  def doOpt() = {

    // pg.paint("opt-raw.dot")

    logger.info("Start collect partitions")
    pg.initPartition()
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

    pg.paintPartConnection(absOutputPath, "opt-pieces-pre-merged.dot")

    pg.writeToMetis(absOutputPath, gpmetis_input_filename)

    val metis_return_file = hiMetis(opt.parallel)

    parseMetisResult(metis_return_file)


    parts.indices.foreach{pid => {
      println(s"Pid: $pid, part size: ${parts(pid).size}")
    }}

    val totalNodeCount = parts.map(_.size).sum

    println(s"Total node count is ${totalNodeCount}, original statement graph has ${pg.validNodes.size} valid nodes")


    // Check correctness

    val partNodeCount = parts.reduce(_ ++ _).size

    println(s"Total node counts in partitions (deduplicated) is $partNodeCount")

    val duplicateNodeCount = parts.map(_.size).sum - partNodeCount
    println(s"Duplication cost: ${duplicateNodeCount} (${(duplicateNodeCount.toFloat / partNodeCount.toFloat) * 100}%)")

//    pg.brief()
//
//    val components = pg.findPartComponents()
//    print(s"Size: ${components.map(_.size)}\n")


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


    val partCount = partResult.max + 1
    parts ++= ArrayBuffer.fill(partCount)(mutable.BitSet())

    partResult.zipWithIndex.foreach{case(partID, pieceID) => {
      if (pg.sinkNodes.indices.contains(pieceID)) {
        parts(partID) ++= pg.trees(pieceID)
      }
    }}
  }



}


object ThreadPartitioner {
  def apply(pg: PartGraph, opt: OptFlags) = {
    new ThreadPartitioner(pg, opt)
  }
}