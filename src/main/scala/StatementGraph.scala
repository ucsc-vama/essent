package essent

import firrtl._
import firrtl.ir._

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._

import collection.mutable.{ArrayBuffer, BitSet}

class StatementGraph extends Graph {
  // Vertex ID -> firrtl statement (Block used for aggregates)
  val idToStmt = ArrayBuffer[Statement]()

  // make sure idToStmt is as big as needed and tracks id of internal graph
  override def getID(vertexName: String) = {
    val id = super.getID(vertexName)
    while (id >= idToStmt.size)
      idToStmt += EmptyStmt
    id
  }

  def buildFromBodies(bodies: Seq[Statement]) {
    val bodyHE = bodies flatMap {
      case b: Block => b.stmts flatMap findDependencesStmt
      case s => findDependencesStmt(s)
    }
    bodyHE foreach { he => {
      addNodeWithDeps(he.name, he.deps)
      idToStmt(getID(he.name)) = he.stmt
    }}
  }

  def nodeSize(id: Int) = flattenStmts(idToStmt(id)).size

  def nonEmptyStmts() = (idToStmt filter { _ != EmptyStmt }).size

  def grabStmts(id: Int) = {
    val stmtsPossiblyWithEmpty = idToStmt(id) match {
      case b: Block => b.stmts
      case az: ActivityZone => az.memberStmts
      case s => Seq(s)
    }
    stmtsPossiblyWithEmpty filter { _ != EmptyStmt }
  }

  def stmtsOrdered(): Seq[Statement] = topologicalSort filter validNodes map idToStmt


  // Mux shadowing
  //----------------------------------------------------------------------------
  def findMuxIDs(): Seq[Int] = idToStmt.zipWithIndex flatMap {
    case (stmt, id) => { stmt match {
      case DefNode(_, _, Mux(_, _, _, _)) => Seq(id)
      case Connect(_, _, Mux(_, _, _, _)) => Seq(id)
      case _ => Seq()
    }}
  }

  // FUTURE: consider creating all MuxShadowed statements on first pass (including nested)
  def coarsenMuxShadows(dontPassSigs: Seq[String]) {
    val muxIDs = findMuxIDs
    val dontPass = BitSet() ++ dontPassSigs.filter(nameToID.contains).map(nameToID)
    def convToStmts(ids: Seq[Int]): Seq[Statement] = ids filter validNodes map idToStmt
    val muxIDToShadows = (muxIDs map { muxID => {
      val muxExpr = grabMux(idToStmt(muxID))
      val tShadow = crawlBack(grabIDs(muxExpr.tval), dontPass, muxID) map nameToID
      val fShadow = crawlBack(grabIDs(muxExpr.fval), dontPass, muxID) map nameToID
      (muxID -> (tShadow, fShadow))
    }}).toMap
    val muxIDSet = muxIDs.toSet
    val nestedMuxes = muxIDToShadows flatMap {
      case (muxID, (tShadow, fShadow)) => (tShadow ++ fShadow) filter muxIDSet
    }
    val topLevelMuxes = muxIDSet -- nestedMuxes
    val muxesWorthShadowing = topLevelMuxes filter { muxID => {
      val (tShadow, fShadow) = muxIDToShadows(muxID)
      tShadow.nonEmpty || fShadow.nonEmpty
    }}
    def replaceMux(newResult: Expression)(e: Expression): Expression = e match {
      case m: Mux => newResult
      case _ => e
    }
    muxesWorthShadowing foreach { muxID => {
      val muxExpr = grabMux(idToStmt(muxID))
      val muxStmtName = idToName(muxID)
      val muxOutputName = findResultName(idToStmt(muxID))
      val (tShadow, fShadow) = muxIDToShadows(muxID)
      val muxOutputStmt = idToStmt(muxID) mapExpr replaceMux(muxExpr.tval)
      // FUTURE: consider adding connects for output within shadows
      idToStmt(muxID) = MuxShadowed(muxOutputName, muxExpr,
                          convToStmts(tShadow) :+ (idToStmt(muxID) mapExpr replaceMux(muxExpr.tval)),
                          convToStmts(fShadow) :+ (idToStmt(muxID) mapExpr replaceMux(muxExpr.fval)))
      mergeStmtsMutably(Seq(muxID) ++ tShadow ++ fShadow)
    }}
  }


  // Topology mutations
  //----------------------------------------------------------------------------
  // assumes merged ID/name will be ids.head
  // assumes caller will set new idToStmt
  def mergeStmtsMutably(ids: Seq[Int]) {
    val mergedID = ids.head
    val idsToRemove = ids.tail
    idsToRemove foreach { id => idToStmt(id) = EmptyStmt }
    val namesToMerge = (Seq(mergedID) ++ idsToRemove) map idToName
    mergeNodesMutably(namesToMerge)
  }

  def mergeNodesSafe(mergeReqs: Seq[Seq[Int]]) {
    mergeReqs foreach { mergeReq => {
      if (mergeReq.size < 2) println("tiny merge req!")
      val zonesStillExist = mergeReq.forall{ idToStmt(_) != EmptyStmt }
      if (zonesStillExist && safeToMergeArb(mergeReq)) {
        idToStmt(mergeReq.head) = Block(mergeReq flatMap grabStmts)
        mergeStmtsMutably(mergeReq)
      }
    }}
  }


  // Zoning
  //----------------------------------------------------------------------------
  def coarsenToMFFCs() {
    val idToMFFC = findMFFCs()
    val mffcMap = Util.groupIndicesByValue(idToMFFC)
    // TODO: shouldn't need to do anything here because invalid nodes all in component -3?
    // NOTE: not all MFFC IDs are validNodes because they weren't originally statements (e.g. regs)
    mffcMap foreach { case (mffcID, memberIDs) => {
      if (mffcID > 0) {
        idToStmt(mffcID) = Block(memberIDs flatMap grabStmts)
        val idsToRemove = memberIDs diff Seq(mffcID)
        mergeStmtsMutably(Seq(mffcID) ++ idsToRemove)
      }
    }}
  }

  def consolidateSourceZones() {
    val sourceIDs = nodeRefIDs filter { id => inNeigh(id).isEmpty && !outNeigh(id).isEmpty }
    println(s"Merging ${sourceIDs.size} source zones")
    addNodeWithDeps("SOURCE_ZONE", Seq())
    idToStmt(getID("SOURCE_ZONE")) = Block(sourceIDs flatMap grabStmts)
    mergeStmtsMutably(Seq(getID("SOURCE_ZONE")) ++ sourceIDs)
  }

  def mergeSingleInputMFFCsToParents() {
    val sourceZoneID = nameToID("SOURCE_ZONE")
    def grabFirstParent(id: Int) = (inNeigh(id) - sourceZoneID).head
    val singleInputIDs = nodeRefIDs filter { id => (inNeigh(id) - sourceZoneID).size == 1}
    val singleInputSet = singleInputIDs.toSet
    val baseSingleInputIDs = singleInputIDs filter { id => !singleInputSet.contains(grabFirstParent(id)) }
    if (baseSingleInputIDs.nonEmpty) {
      println(s"Merging up ${baseSingleInputIDs.size} single-input zones")
      baseSingleInputIDs foreach { childID => {
        val parentID = grabFirstParent(childID)
        idToStmt(parentID) = Block(grabStmts(parentID) ++ grabStmts(childID))
        mergeStmtsMutably(Seq(parentID, childID))
      }}
      mergeSingleInputMFFCsToParents()
    }
  }

  def mergeSmallSiblings(smallZoneCutoff: Int = 10) {
    val smallZoneIDs = nodeRefIDs filter { id => {
      val idSize = nodeSize(id)
      (idSize > 0) && (idSize < smallZoneCutoff)
    }}
    val inputsAndIDPairs = smallZoneIDs map { id => {
      val inputsCanonicalized = inNeigh(id).toSeq.sorted
      (inputsCanonicalized, id)
    }}
    val inputsToSiblings = Util.groupByFirst(inputsAndIDPairs)
    val mergesToConsider = inputsToSiblings.toSeq flatMap { case (inputIDs, siblingIDs) => {
      if ((siblingIDs.size > 1) && safeToMergeArb(siblingIDs)) Seq(siblingIDs)
      else Seq()
    }}
    if (mergesToConsider.nonEmpty) {
      println(s"Attempting to merge ${mergesToConsider.size} groups of small siblings")
      mergeNodesSafe(mergesToConsider)
      mergeSmallSiblings(smallZoneCutoff)
    }
  }

  // merges small zones based on fraction of shared inputs
  def mergeSmallZones(smallZoneCutoff: Int = 20, mergeThreshold: Double = 0.5) {
    val smallZoneIDs = nodeRefIDs filter { id => {
      val idSize = nodeSize(id)
      (idSize > 0) && (idSize < smallZoneCutoff)
    }}
    def overlapSize(idA: Int, idB: Int): Int = inNeigh(idA).intersect(inNeigh(idB)).size
    val sourceZoneID = nameToID("SOURCE_ZONE")
    val mergesToConsider = smallZoneIDs flatMap { id => {
      val numInputs = inNeigh(id).size.toDouble
      val siblings = ((inNeigh(id) - sourceZoneID) flatMap outNeigh).distinct - id
      val sibsScored = siblings map {
        sibID => (overlapSize(id, sibID) / numInputs, sibID)
      }
      val choices = sibsScored filter { _._1 >= mergeThreshold }
      val choicesOrdered = choices.sortWith{_._1 > _._1}
      val topChoice = choicesOrdered.find {
        case (score, sibID) => safeToMergeArb(Seq(sibID, id))
      }
      if (topChoice.isEmpty) Seq()
      else Seq(Seq(topChoice.get._2, id))
    }}
    println(s"Small zones: ${smallZoneIDs.size}")
    println(s"Worthwhile merges: ${mergesToConsider.size}")
    if (mergesToConsider.nonEmpty) {
      mergeNodesSafe(mergesToConsider)
      mergeSmallZones(smallZoneCutoff, mergeThreshold)
    }
  }

  def translateBlocksIntoZones(keepAvail: Set[String]) {
    val blockIDs = nodeRefIDs filter { idToStmt(_).isInstanceOf[Block] }
    val idToMemberStmts: Map[Int,Seq[Statement]] = (blockIDs map { id => {
      val members = idToStmt(id) match {
        case b: Block => b.stmts
        case _ => throw new Exception("matched a non-block statement")
      }
      (id -> members)
    }}).toMap
    val idToHE = idToMemberStmts mapValues { members => members flatMap findDependencesStmt }
    val idToMemberNames = idToHE mapValues { zoneHE => zoneHE map { _.name } }
    val sourceZoneMembers = if (idToName.contains("SOURCE_ZONE"))
                              idToMemberNames(nameToID("SOURCE_ZONE")).toSeq
                            else Seq[String]()
    val idToInputNames = idToHE map { case (id, zoneHE) => {
      val zoneDepNames = (zoneHE flatMap { _.deps }).distinct diff sourceZoneMembers
      val externalDepNames = zoneDepNames diff idToMemberNames(id)
      (id -> externalDepNames)
    }}
    val inputNameToConsumingZoneIDs = Util.groupByFirst(idToInputNames.toSeq flatMap {
      case (id, inputNames) => inputNames map { (_, id) }
    })
    blockIDs foreach { id => {
      val zoneName = idToName(id)
      val memberSet = idToMemberNames(id).toSet
      val requestedOutputs = memberSet.intersect(keepAvail)
      val consumedOutputs = memberSet.intersect(inputNameToConsumingZoneIDs.keys.toSet)
      // NOTE: can be overlaps, but set addition removes differences
      val outputNameSet = if (zoneName != "SOURCE_ZONE") requestedOutputs ++ consumedOutputs else Set[String]()
      val outputConsumers = outputNameSet map { outputName => {
        val consumerIDs = inputNameToConsumingZoneIDs.getOrElse(outputName, Seq())
        (outputName, consumerIDs map idToName)
      }}
      val outputTypes = idToHE(id) flatMap {
        he => if (outputNameSet.contains(he.name)) Seq((he.name -> findResultType(he.stmt)))
              else Seq()
      }
      idToStmt(id) = ActivityZone(zoneName, idToInputNames(id), idToMemberStmts(id),
                                  idToMemberNames(id), outputConsumers.toMap, outputTypes.toMap)
    }}
  }

  def coarsenIntoZones(keepAvail: Seq[String] = Seq()) {
    // Not worrying about dead zones for now
    val toApply = Seq(
      ("mffc", {sg: StatementGraph => sg.coarsenToMFFCs()}),
      ("source", {sg: StatementGraph => sg.consolidateSourceZones()}),
      ("single", {sg: StatementGraph => sg.mergeSingleInputMFFCsToParents()}),
      ("siblings", {sg: StatementGraph => sg.mergeSmallSiblings()}),
      ("small", {sg: StatementGraph => sg.mergeSmallZones(20, 0.5)}),
      ("small2", {sg: StatementGraph => sg.mergeSmallZones(40, 0.25)}),
      ("IR", {sg: StatementGraph => sg.translateBlocksIntoZones(keepAvail.toSet)})
    )
    toApply foreach { case(label, func) => {
      val startTime = System.currentTimeMillis()
      func(this)
      val stopTime = System.currentTimeMillis()
      println(s"[$label] took: ${stopTime - startTime}")
      println(s"Down to ${nonEmptyStmts()} statement blocks")
    }}
    analyzeZoningQuality()
  }


  // Zone info
  //----------------------------------------------------------------------------
  def getZoneOutputTypes(): Seq[(String,Type)] = {
    val allZoneOutputTypes = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.outputTypes.toSeq
      case _ => Seq()
    }}
    allZoneOutputTypes
  }

  def getExternalZoneInputs(): Seq[String] = {
    val allZoneInputs = (validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}).toSet
    val allZoneOutputs = (getZoneOutputTypes() map { _._1 }).toSet
    (allZoneInputs -- allZoneOutputs).toSeq
  }

  def getZoneInputMap(): Map[String,Seq[String]] = {
    val allZoneInputs = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.inputs map { (_, idToName(id)) }
      case _ => Seq()
    }}
    Util.groupByFirst(allZoneInputs)
  }

  def getZoneNames(): Seq[String] = {
    validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Seq(az.name)
      case _ => Seq()
    }}
  }

  def getSourceZone(): Option[ActivityZone] = {
    if (nameToID.contains("SOURCE_ZONE")) {
      idToStmt(nameToID("SOURCE_ZONE")) match {
        case az: ActivityZone => Some(az)
        case _ => throw new Exception("Non-zone node called SOURCE_ZONE")
      }
    } else None
  }

  def analyzeZoningQuality() {
    val numZones = getZoneNames().size
    println(s"Zones: $numZones")
    val numStmtsInZones = (nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Some(az.memberStmts.size)
      case _ => None
    }}).sum
    // NOTE: Compiler withholds some statements from zoning process
    val numStmtsTotal = (nodeRefIDs map nodeSize).sum
    val percNodesInZones = 100d * numStmtsInZones / numStmtsTotal
    println(f"Nodes in zones: $numStmtsInZones ($percNodesInZones%2.1f%%)")
    val numEdgesOrig = (nodeRefIDs flatMap {
      id => grabStmts(id) flatMap {
        stmt => findDependencesStmt(stmt) map { _.deps.size }
      }
    }).sum
    val allOutputMaps = nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.outputConsumers.toSeq
      case _ => None
    }}
    val numOutputsUnique = allOutputMaps.size
    val numOutputsFlat = (allOutputMaps map { _._2.size }).sum
    val percEdgesInZones = 100d * (numEdgesOrig - numOutputsFlat) / numEdgesOrig
    println(f"Edges in zones: ${numEdgesOrig - numOutputsFlat} ($percEdgesInZones%2.1f%%)")
    println(f"Nodes/zone: ${numStmtsTotal.toDouble/numZones}%.1f")
    println(f"Outputs/zone: ${numOutputsUnique.toDouble/numZones}%.1f")
  }


  // Register merging
  //----------------------------------------------------------------------------
  def mergeRegUpdatesIntoZones(regsToConsider: Seq[String]): Seq[String] = {
    // FUTURE: consider converting to ids internally to speed up
    val inputNameToConsumers = getZoneInputMap()
    val regNamesSet = regsToConsider.toSet
    val regNameToZoneName = (nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => {
        val zoneName = idToName(id)
        val regsInZone = az.memberNames map { _.replaceAllLiterally("$next","") } filter regNamesSet
        regsInZone map { (_, zoneName) }
      }
      case _ => Seq()
    }}).toMap
    val mergedRegs = regsToConsider flatMap { regName => {
      val regWriterZoneID = nameToID(regNameToZoneName(regName))
      val regReaderZoneIDs = inputNameToConsumers(regName) map nameToID
      val okToMerge = regReaderZoneIDs forall { readerID => !pathExists(regWriterZoneID, readerID) }
      if (okToMerge) {
        val regWriterZoneName = idToName(regWriterZoneID)
        regReaderZoneIDs map idToName filter { _ != regWriterZoneName } foreach { readerName => {
          if (!outNeigh(nameToID(readerName)).contains(regWriterZoneID))
            addEdge(readerName, regWriterZoneName)
        }}
        Seq(regName)
      } else Seq()
    }}
    println(s"Was able to merge ${mergedRegs.size}/${regsToConsider.size} of mergeable regs")
    mergedRegs
  }

  def updateMergedRegWrites(mergedRegs: Seq[String]) {
    def updateConnect(targName: String)(s: Statement): Statement = {
      val result = s match {
        case c: Connect => {
          if (findResultName(c) == targName + "$next") {
            val regNameWithoutNext = c.loc match {
              case w: WRef => w.copy(name = w.name.replaceAllLiterally("$next",""))
              case w: WSubField => w.copy(name = w.name.replaceAllLiterally("$next",""))
            }
            RegUpdate(NoInfo, regNameWithoutNext, c.expr)
          } else c
        }
        case _ => s
      }
      result mapStmt updateConnect(targName)
    }
    mergedRegs foreach { regName => {
      val regWriteID = nameToID(regName + "$next")
      idToStmt(regWriteID) = updateConnect(regName)(idToStmt(regWriteID))
    }}
  }
}


object StatementGraph {
  def apply(bodies: Seq[Statement]) = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg
  }
}