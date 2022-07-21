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

  val idToPieceID = ArrayBuffer[NodeID]()

  val idToNodeWeight = ArrayBuffer[NodeID]()

  val sinkNodes = ArrayBuffer[NodeID]()
  var trees = mutable.ArrayBuffer[BitSet]()
  val pieces = mutable.ArrayBuffer[BitSet]()


  val hg = new HyperGraph()


  def buildFromGraph(sg: StatementGraph): Unit = {
    idToTreeID.appendAll(ArrayBuffer.fill(sg.numNodes())(mutable.Set[NodeID]()))
    idToPieceID ++= ArrayBuffer.fill(sg.numNodes())(-1)

    idToNodeWeight.appendAll(ArrayBuffer.fill(sg.numNodes())(-1))

    // -1 => unvisited
    // -2 => invalid
    sg.idToStmt.indices.filterNot(sg.validNodes.contains).foreach{id => idToPieceID(id) = -2}


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

  def initTrees(): Unit = {

    val treeCache = mutable.HashMap[NodeID, BitSet]()

    def collectTree(seed: NodeID): BitSet = {
      if (!treeCache.contains(seed)) {
        val depNodes = idToStmt(seed) match {
          case inv if (!validNodes.contains(seed)) => BitSet() // invalid
          case d: DefRegister => BitSet() // Stop at register read
          case _ => BitSet(seed) ++ (inNeigh(seed) flatMap {collectTree})
        }

        if (outNeigh(seed).length > 1) {
          treeCache(seed) = depNodes
        }

        depNodes
      } else treeCache(seed)
    }

    sinkNodes ++= validNodes.filter(outNeigh(_).isEmpty)

    val collectedParts = sinkNodes.map{collectTree}

    trees.clear()
    trees ++= collectedParts
  }

  def initPieces() = {

    trees.indices.foreach{partID => {trees(partID).foreach{ nodeID => {
      idToTreeID(nodeID) += partID
    }}}}


    // Assuming pieces(pid) is an empty BitSet
    def findPiece(pid: NodeID)(seed: NodeID): Unit = {
      if (idToPieceID(seed) == -1) {
        pieces(pid) += seed
        idToPieceID(seed) = pid
        val connectedVertecies = (inNeigh(seed) ++ outNeigh(seed)).filter(idToPieceID(_) == -1)
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





  def calculateNodeWeight(id: NodeID): Int = {
    if (idToNodeWeight(id) != -1) {
      return idToNodeWeight(id)
    }

    val MemReadWeight = 0
    val MemWriteWeight = 1
    val RegReadWeight = 0
    val RegWriteWeight = 15
    // IO R/W weight: ExtIO(top) and ExtModule
    val IOReadWeight = 0
    val IOWriteWeight = 0
    val PrimOpWeight = 1
    val MuxOpWeight = 3
    val NodeKindWeight = 3
    val ConnectWeight = 0
    val DefNodeWeight = 0

    def exprWeight(e: Expression, is_lvalue: Boolean): Int = e match {

      case r: Reference => r.kind match {
        case firrtl.PortKind => if (is_lvalue) IOWriteWeight else IOReadWeight
        case firrtl.MemKind => if (is_lvalue) {
          throw new Exception("Register write should not happen here")
        } else MemReadWeight
        case firrtl.RegKind => if (is_lvalue) {
          throw new Exception("Register write should not happen here")
        } else RegReadWeight
        case firrtl.InstanceKind => if (is_lvalue) IOWriteWeight else IOReadWeight
        // Connect to other nodes will be handled as dependency, ignore here
        case firrtl.NodeKind => NodeKindWeight
        case _ => throw new Exception("Not supported yet")
      }
      case u: UIntLiteral => 0
      case s: SIntLiteral => 0

      case op: DoPrim => {
        PrimOpWeight + (op.args map{exprWeight(_, is_lvalue = false)}).sum
      }

      case m: Mux => {
        val condWeight = exprWeight(m.cond, is_lvalue = false)
        val tvalWeight = exprWeight(m.tval, is_lvalue = false)
        val fvalWeight = exprWeight(m.fval, is_lvalue = false)
        MuxOpWeight + condWeight + ((tvalWeight + fvalWeight) / 2)
      }

      case sf: SubField => exprWeight(sf.expr, is_lvalue) + PrimOpWeight

      // SubAccess: A field in memory
      case sa: SubAccess => {
        if (is_lvalue) {
          throw new Exception("A SubAccess cannot be lvalue")
        }
        exprWeight(sa.expr, is_lvalue = false) + exprWeight(sa.index, is_lvalue = false)
      }

      case _ => throw new Exception("Unknown expression type")
    }


    val currentWeight = idToStmt(id) match {
      case d: DefInstance => throw new Exception("DefInstance should not exists here")
      case d: DefRegister => throw new Exception("DefRegister should not exists here")
      case m: DefMemory => throw new Exception("DefMemory should not exists here")

      case st: Stop => 0
      case pr: Print => 0
      case EmptyStmt => 0

      case mw: MemWrite => MemWriteWeight + exprWeight(mw.wrEn, is_lvalue = false)
      case ru: RegUpdate => RegWriteWeight + exprWeight(ru.expr, is_lvalue = false)

      case c: Connect => {
        ConnectWeight + exprWeight(c.loc, is_lvalue = true) + exprWeight(c.expr, is_lvalue = false)
      }

      case d: DefNode => DefNodeWeight + exprWeight(d.value, is_lvalue = false)

      case _ => throw new Exception("Unknown IR type")
    }

    idToNodeWeight(id) = currentWeight
    currentWeight
  }

  def calculatePieceWeight(piece: BitSet) = {

    // TODO : is this correct?
    val pieceSinkNodes = piece.toSeq.filter{id => {(outNeigh(id).toSet intersect piece).isEmpty}}

    val visitedNodes = mutable.Set[NodeID]()


    def stmtWeight(sinkId: NodeID): Int = {

      if (visitedNodes.contains(sinkId)) 0 else {
        visitedNodes += sinkId

        if (idToNodeWeight(sinkId) == -1) {
          idToNodeWeight(sinkId) = calculateNodeWeight(sinkId)
        }


        val currentWeight = idToNodeWeight(sinkId)

        currentWeight + ((inNeigh(sinkId) filter validNodes filter piece) map stmtWeight).sum
      }
    }

    // Weight should be at least 1 to make KaHyPar happy
    (pieceSinkNodes map stmtWeight).sum + 1
  }

  def calculatePieceWeight_Trace(piece: BitSet) = {


    // TODO : is this correct?
    val pieceSinkNodes = piece.toSeq.filter{id => {(outNeigh(id).toSet intersect piece).isEmpty}}

    val visitedNodes = mutable.Set[NodeID]()



    def exprWeight(e: Expression, is_lvalue: Boolean): Seq[String] = e match {

      case r: Reference => r.kind match {
        case firrtl.PortKind => if (is_lvalue) Seq("IOWriteWeight") else Seq("IOReadWeight")
        case firrtl.MemKind => if (is_lvalue) {
          throw new Exception("Register write should not happen here")
        } else Seq("MemReadWeight")
        case firrtl.RegKind => if (is_lvalue) {
          throw new Exception("Register write should not happen here")
        } else Seq("RegReadWeight")
        case firrtl.InstanceKind => if (is_lvalue) Seq("IOWriteWeight") else Seq("IOReadWeight")
        // Connect to other nodes will be handled as dependency, ignore here
        case firrtl.NodeKind => Seq("NodeKindWeight")
        case _ => throw new Exception("Not supported yet")
      }
      case u: UIntLiteral => Seq()
      case s: SIntLiteral => Seq()

      case op: DoPrim => {
        Seq("PrimOpWeight") ++ (op.args flatMap {exprWeight(_, is_lvalue = false)})
      }

      case m: Mux => {
        val condWeight = exprWeight(m.cond, is_lvalue = false)
        val tvalWeight = exprWeight(m.tval, is_lvalue = false)
        val fvalWeight = exprWeight(m.fval, is_lvalue = false)
        Seq("MuxOpWeight") ++ condWeight ++ tvalWeight ++ fvalWeight
      }

      case sf: SubField => exprWeight(sf.expr, is_lvalue) ++ Seq("PrimOpWeight")

      // SubAccess: A field in memory
      case sa: SubAccess => {
        if (is_lvalue) {
          throw new Exception("A SubAccess cannot be lvalue")
        }
        exprWeight(sa.expr, is_lvalue = false) ++ exprWeight(sa.index, is_lvalue = false)
      }

      case _ => throw new Exception("Unknown expression type")
    }

    def stmtWeight(sinkId: NodeID): Seq[String] = {
      if (visitedNodes.contains(sinkId)) Seq() else {
        visitedNodes += sinkId

        val currentWeight = idToStmt(sinkId) match {
          case d: DefInstance => throw new Exception("DefInstance should not exists here")
          case d: DefRegister => throw new Exception("DefRegister should not exists here")
          case m: DefMemory => throw new Exception("DefMemory should not exists here")

          case st: Stop => Seq()
          case pr: Print => Seq()
          case EmptyStmt => Seq()

          case mw: MemWrite => Seq("MemWriteWeight") ++ exprWeight(mw.wrEn, is_lvalue = false)
          case ru: RegUpdate => Seq("RegWriteWeight") ++ exprWeight(ru.expr, is_lvalue = false)

          case c: Connect => {
            exprWeight(c.loc, is_lvalue = true) ++ exprWeight(c.expr, is_lvalue = false) ++ Seq("ConnectWeight")
          }

          case d: DefNode => exprWeight(d.value, is_lvalue = false) ++ Seq("DefNodeWeight")

          case _ => throw new Exception("Unknown IR type")
        }

        currentWeight ++ ((inNeigh(sinkId) filter validNodes filter piece) flatMap  stmtWeight)
      }
    }

    // Weight should be at least 1 to make KaHyPar happy
    val raw = pieceSinkNodes flatMap stmtWeight

    val ret = mutable.HashMap[String, Int]()
    for (e <- raw) {
      if (ret.contains(e)) {
        ret(e) += 1
      } else {
        ret(e) = 1
      }
    }

    ret
  }




  def updateHyperGraph(): Unit = {
    val pieceWeights = pieces.map(calculatePieceWeight)
    // each node in a piece has same treeIds so just pick any one
    val hePinCount = pieces.map{p => idToTreeID(p.head).size}

    // Add nodes
    for (elem <- trees.indices) {
      val weight = pieceWeights(elem)
      val connectPieces = (trees(elem).map(idToPieceID) - elem).toSeq
      val connectPieceWeights = connectPieces.map {pid => {
        val pinCount = hePinCount(pid)
        val pieceWeight = pieceWeights(pid)
        (pieceWeight / pinCount)
      }}

      hg.addNode(elem, weight + connectPieceWeights.sum)
    }

    // Add edges
    for (elem <- pieces.indices) {
      if (elem >= trees.length) {
        // For all edges
        val edgeWeight = pieceWeights(elem)
        val edgeNodes = idToTreeID(pieces(elem).head).to[ArrayBuffer]

        hg.addEdge(edgeNodes, edgeWeight)
      }
    }
  }







  def writeTohMetis(dir: String, fileName: String) = {
    val writer = new FileWriter(new File(dir, fileName))

    def writeLine(dat: Seq[Any]) = {
      writer write(dat.mkString(" ") + "\n")
    }

    // header
    writeLine(Seq(s"${hg.edges.length}", s"${hg.nodes.length}", "11"))

    // edges
    hg.edges.indices.foreach{eid => {
      // node id + 1 to make hMetis happy
      val edgeNodes = hg.edges(eid).map{_+1}
      val edgeWeight = hg.edgeWeight(eid)
      writeLine(Seq(edgeWeight) ++ edgeNodes)
    }}

    // nodes
    hg.nodeWeight.foreach{ weight => {
      writeLine(Seq(weight))
    }}

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


  val hmetis_input_filename = "parts.hmetis"

  //val kahypar_path = "/Users/hwang/project/kahypar/build/kahypar/application/KaHyPar"
  val kahypar_path = "KaHyPar"
  val kahypar_config_filename = "KaHyPar.config"
//  val kahypar_preset = "/Users/hwang/project/kahypar/config/km1_kKaHyPar_sea20.ini"

  val absOutputPath: String = if (java.nio.file.Paths.get(opt.outputDir()).isAbsolute) opt.outputDir() else (os.pwd/os.RelPath(opt.outputDir())).toString()

  val parts = ArrayBuffer[BitSet]()
  val parts_read = ArrayBuffer[ArrayBuffer[Int]]()
  val parts_write = ArrayBuffer[ArrayBuffer[Int]]()


  def doOpt() = {


    logger.info("Collect trees")
    val startTime_tree = System.currentTimeMillis()
    pg.initTrees()
    val endTime_tree = System.currentTimeMillis()
    val elapse_tree = (endTime_tree - startTime_tree)
    logger.info(s"Done collect trees in $elapse_tree ms")

    logger.info(s"Found ${pg.sinkNodes.size} sink nodes")

    logger.info("Collect pieces")
    val startTime_pieces = System.currentTimeMillis()
    pg.initPieces()
    val endTime_pieces = System.currentTimeMillis()
    val elapse_pieces = (endTime_pieces - startTime_pieces)
    logger.info(s"Done collect pieces in $elapse_pieces ms")

    logger.info("Update hyper graph")
    val startTime_hg = System.currentTimeMillis()
    pg.updateHyperGraph()
    val endTime_hg = System.currentTimeMillis()
    val elapse_hg = (endTime_hg - startTime_hg)
    logger.info(s"Done hyper graph updating in $elapse_hg ms")


    logger.info("Write to hMetis output file")
    val startTime_hmetis = System.currentTimeMillis()
    pg.writeTohMetis(absOutputPath, hmetis_input_filename)
    val endTime_hmetis = System.currentTimeMillis()
    val elapse_hmetis = (endTime_hmetis - startTime_hmetis)
    logger.info(s"Done output in $elapse_hmetis ms")


    logger.info("Call KaHyPar")
    val startTime_kahypar = System.currentTimeMillis()
    val metis_return_file = hiKaHyPar(opt.parallel)
    val endTime_kahypar = System.currentTimeMillis()
    val elapse_kahypar = (endTime_kahypar - startTime_kahypar)
    logger.info(s"KaHyPar spend $elapse_kahypar ms")

    logger.info("Parse result")
    parseMetisResult(metis_return_file)

    parts.indices.foreach{pid => {
      println(s"Pid: $pid, part size: ${parts(pid).size}, part weight: ${pg.calculatePieceWeight(parts(pid))}")
    }}

    // Print out weight calculation trace

    println("StartJSON")
    println("{")
    parts.indices.foreach{pid => {
      val trace = pg.calculatePieceWeight_Trace(parts(pid))
      println("    {")
      for ((k, v) <- trace) {
        println(s"""        \"${k}\" : ${v},  """)
      }
      println("    },")
    }}
    println("}")
    println("EndJSON")

    val totalNodeCount = parts.map(_.size).sum

    println(s"Total node count is ${totalNodeCount}, original statement graph has ${pg.validNodes.size} valid nodes")


    val partNodeCount = parts.reduce(_ ++ _).size
    val duplicateNodeCount = parts.map(_.size).sum - partNodeCount

    println(s"Total node counts in partitions (deduplicated) is $partNodeCount")
    println(s"Duplication cost: ${duplicateNodeCount} (${(duplicateNodeCount.toFloat / partNodeCount.toFloat) * 100}%)")

    val smallestSize = parts.map(_.size).min
    val largestSize = parts.map(_.size).max
    println(s"Partition size: max: ${largestSize}, min: ${smallestSize}, avg: ${partNodeCount / parts.length}")


    val stmtsIdOrdered = TopologicalSort(pg)
    def isReadStmtId(id: NodeID) = pg.idToStmt(id) match {
      case dr: DefRegister => true
      case dm: DefMemory => true
      // EmptyStmt exists in source nodes but not actually a read
      // case EmptyStmt => true
      case _ => false
    }
    def isWriteStmtId(id: NodeID) = pg.idToStmt(id) match {
      case ru: RegUpdate => true
      case mw: MemWrite => true
      // Following IR exists in sink nodes not not actually a write
//      case p: Print => true
//      case s: Stop => true
//      case c: Connect => true
      case _ => false
    }

    val readStmtIdsOrdered = stmtsIdOrdered.collect{case id if isReadStmtId(id) => id}
    val writeStmtIdsOrdered = stmtsIdOrdered.collect{case id if isWriteStmtId(id) => id}

    parts.foreach {part => {
      val part_source = part.flatMap(pg.inNeigh).toSet -- part
      val part_sink = part.filter(pg.outNeigh(_).isEmpty).toSet

      val part_read_ordered = readStmtIdsOrdered.filter(part_source.contains)
      val part_write_ordered = writeStmtIdsOrdered.filter(part_sink.contains)


      parts_read.append(part_read_ordered)
      parts_write.append(part_write_ordered)

    }}

    logger.info("Done")

  }



  def hiKaHyPar(desiredParts: Int) = {

    val kahypar_preset = """# general
                           |mode=direct
                           |objective=km1
                           |seed=-1
                           |cmaxnet=1000
                           |vcycles=0
                           |# main -> preprocessing -> min hash sparsifier
                           |p-use-sparsifier=true
                           |p-sparsifier-min-median-he-size=28
                           |p-sparsifier-max-hyperedge-size=1200
                           |p-sparsifier-max-cluster-size=10
                           |p-sparsifier-min-cluster-size=2
                           |p-sparsifier-num-hash-func=5
                           |p-sparsifier-combined-num-hash-func=100
                           |# main -> preprocessing -> community detection
                           |p-detect-communities=true
                           |p-detect-communities-in-ip=true
                           |p-reuse-communities=false
                           |p-max-louvain-pass-iterations=100
                           |p-min-eps-improvement=0.0001
                           |p-louvain-edge-weight=hybrid
                           |# main -> coarsening
                           |c-type=ml_style
                           |c-s=1
                           |c-t=160
                           |# main -> coarsening -> rating
                           |c-rating-score=heavy_edge
                           |c-rating-use-communities=true
                           |c-rating-heavy_node_penalty=no_penalty
                           |c-rating-acceptance-criterion=best_prefer_unmatched
                           |c-fixed-vertex-acceptance-criterion=fixed_vertex_allowed
                           |# main -> initial partitioning
                           |i-mode=recursive
                           |i-technique=multi
                           |# initial partitioning -> coarsening
                           |i-c-type=ml_style
                           |i-c-s=1
                           |i-c-t=150
                           |# initial partitioning -> coarsening -> rating
                           |i-c-rating-score=heavy_edge
                           |i-c-rating-use-communities=true
                           |i-c-rating-heavy_node_penalty=no_penalty
                           |i-c-rating-acceptance-criterion=best_prefer_unmatched
                           |i-c-fixed-vertex-acceptance-criterion=fixed_vertex_allowed
                           |# initial partitioning -> initial partitioning
                           |i-algo=pool
                           |i-runs=20
                           |# initial partitioning -> bin packing
                           |i-bp-algorithm=worst_fit
                           |i-bp-heuristic-prepacking=false
                           |i-bp-early-restart=true
                           |i-bp-late-restart=true
                           |# initial partitioning -> local search
                           |i-r-type=twoway_fm
                           |i-r-runs=-1
                           |i-r-fm-stop=simple
                           |i-r-fm-stop-i=50
                           |# main -> local search
                           |r-type=kway_fm_hyperflow_cutter_km1
                           |r-runs=-1
                           |r-fm-stop=adaptive_opt
                           |r-fm-stop-alpha=1
                           |r-fm-stop-i=350
                           |# local_search -> flow scheduling and heuristics
                           |r-flow-execution-policy=exponential
                           |# local_search -> hyperflowcutter configuration
                           |r-hfc-size-constraint=mf-style
                           |r-hfc-scaling=16
                           |r-hfc-distance-based-piercing=true
                           |r-hfc-mbc=true
                           |""".stripMargin

    // Write config file
    val writer = new FileWriter(new File(absOutputPath, kahypar_config_filename))
    writer write kahypar_preset
    writer.close()

    val kahypar_imbalance_factor = 0.05
    val kahypar_seed = -1

    val cmd = List(kahypar_path,
      "-h", (os.Path(absOutputPath)/hmetis_input_filename).toString(),
      "-k", desiredParts.toString,
      "-e", kahypar_imbalance_factor.toString,
      "-p", (os.Path(absOutputPath)/kahypar_config_filename).toString(),
      "--seed", kahypar_seed.toString,
      "-w", "true",

      // mandatory arguments, even already given in preset file
      "--mode", "direct",
      "--objective", "km1",
    )

    val r = os.proc(cmd).call(check = false)

    println("KayHyPar output:")
    println("*" * 50)

    print(r.out.string)
    println("*" * 50)

    assert(r.exitCode == 0, s"Return code is not 0, ${r.exitCode} received.")



    (os.Path(absOutputPath)/(hmetis_input_filename
      + ".part"
      + desiredParts.toString
      + ".epsilon"
      + kahypar_imbalance_factor.toString
      + ".seed"
      + kahypar_seed.toString
      + ".KaHyPar"
      )).toString()
  }


  def parseMetisResult(fileName: String) = {

    logger.info("Partitioner: Read " + fileName)

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