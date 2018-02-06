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

  def stmtsOrdered(): Seq[Statement] = {
    topologicalSort filter { idToStmt(_) != EmptyStmt } map idToStmt
    // topologicalSort filter validNodes map idToStmt
  }

  def updateMergedRegWrites(mergedRegs: Seq[String]) {
    mergedRegs foreach { regName => {
      val regWriteName = regName + "$next"
      val regWriteID = nameToID(regWriteName)
      val newName = s"if (update_registers) $regName"
      idToStmt(regWriteID) = replaceNamesStmt(Map(regWriteName -> newName))(idToStmt(regWriteID))
    }}
  }

  def findMuxIDs(): Seq[Int] = idToStmt.zipWithIndex flatMap {
    case (stmt, id) => { stmt match {
      case DefNode(_, _, Mux(_, _, _, _)) => Seq(id)
      case Connect(_, _, Mux(_, _, _, _)) => Seq(id)
      case _ => Seq()
    }}
  }

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

  // FUTURE: consider creating all MuxShadowed statements on first pass (including nested)
  def coarsenMuxShadows(dontPassSigs: Seq[String]) {
    val muxIDs = findMuxIDs
    val dontPass = BitSet() ++ dontPassSigs.filter(nameToID.contains).map(nameToID)
    def convToStmts(ids: Seq[Int]): Seq[Statement] = ids map idToStmt
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
      !(tShadow.isEmpty && fShadow.isEmpty)
    }}
    muxesWorthShadowing foreach { muxID => {
      val muxExpr = grabMux(idToStmt(muxID))
      val muxStmtName = idToName(muxID)
      val muxOutputName = findResultName(idToStmt(muxID))
      val (tShadow, fShadow) = muxIDToShadows(muxID)
      // FUTURE: consider adding connects for output within shadows
      idToStmt(muxID) = MuxShadowed(muxOutputName, muxExpr, convToStmts(tShadow), convToStmts(fShadow))
      mergeStmtsMutably(Seq(muxID) ++ tShadow ++ fShadow)
    }}
  }

  def coarsenToMFFCs() {
    val idToMFFC = findMFFCs()
    val mffcMap = Util.groupIndicesByValue(idToMFFC)
    // NOTE: not all MFFC IDs are validNodes because they weren't originally statements (e.g. regs)
    mffcMap foreach { case (mffcID, memberIDs) => {
      idToStmt(mffcID) = Block(memberIDs map idToStmt)
      val idsToRemove = memberIDs diff Seq(mffcID)
      mergeStmtsMutably(Seq(mffcID) ++ idsToRemove)
    }}
  }

  def consolidateSourceZones() {
    val sourceIDs = nodeRefIDs filter { id => inNeigh(id).isEmpty && !outNeigh(id).isEmpty }
    println(s"Merging ${sourceIDs.size} source zones")
    addNodeWithDeps("SOURCE_ZONE", Seq())
    // FUTURE: consider flattening blocks
    idToStmt(getID("SOURCE_ZONE")) = Block(sourceIDs map idToStmt)
    mergeStmtsMutably(Seq(getID("SOURCE_ZONE")) ++ sourceIDs)
  }

  def mergeSingleInputMFFCsToParents() {
    val sourceZoneID = nameToID("SOURCE_ZONE")
    def grabFirstParent(id: Int) = (inNeigh(id) - sourceZoneID).head
    val singleInputIDs = nodeRefIDs filter { id => (inNeigh(id) - sourceZoneID).size == 1}
    val singleInputSet = singleInputIDs.toSet
    val baseSingleInputIDs = singleInputIDs filter { id => !singleInputSet.contains(grabFirstParent(id)) }
    if (!baseSingleInputIDs.isEmpty) {
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
    if (!mergesToConsider.isEmpty) {
      println(s"Attempting to merge ${mergesToConsider.size} groups of small siblings")
      mergeNodesSafe(mergesToConsider)
      mergeSmallSiblings(smallZoneCutoff)
    }
  }

  def nodeSize(id: Int) = flattenStmts(idToStmt(id)).size

  def nonEmptyStmts() = (idToStmt filter { _ != EmptyStmt }).size

  def grabStmts(id: Int) = idToStmt(id) match {
    case b: Block => b.stmts
    case s => Seq(s)
  }

  // like mergeSmallZones2
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
    if (!mergesToConsider.isEmpty) {
      mergeNodesSafe(mergesToConsider)
      mergeSmallZones(smallZoneCutoff, mergeThreshold)
    }
  }

  def translateBlocksIntoZones() {
    val blockIDs = nodeRefIDs filter { idToStmt(_).isInstanceOf[Block] }
    val idToMembers: Map[Int,Seq[Statement]] = (blockIDs map { id => {
      val members = idToStmt(id) match {
        case b: Block => b.stmts
        case _ => throw new Exception("matched a non-block statement")
      }
      (id -> members)
    }}).toMap
    val idToHE = idToMembers mapValues { members => members flatMap findDependencesStmt }
    val idToMemberNames = idToHE mapValues { zoneHE => zoneHE map { _.name } }
    val idToInputNames = idToHE map { case (id, zoneHE) => {
      val zoneDepNames = zoneHE flatMap { _.deps }
      val externalDepNames = zoneDepNames.distinct diff idToMemberNames(id)
      (id -> externalDepNames)
    }}
    val inputNameToConsumingZoneIDs = Util.groupByFirst(idToInputNames.toSeq flatMap {
      case (id, inputNames) => inputNames map { (_, id) }
    })
    blockIDs foreach { id => {
      val outputNameSet = idToMemberNames(id).toSet.intersect(inputNameToConsumingZoneIDs.keys.toSet)
      val outputConsumers = outputNameSet map {
        outputName => (outputName, inputNameToConsumingZoneIDs(outputName) map idToName)
      }
      val outputTypes = idToHE(id) flatMap {
        he => if (outputNameSet.contains(he.name)) Seq((he.name -> findResultType(he.stmt)))
              else Seq()
      }
      idToStmt(id) = ActivityZone(idToName(id), idToMembers(id), outputConsumers.toMap, outputTypes.toMap)
    }}
  }

  def coarsenIntoZones() {
    // Not worrying about dead zones for now
    val toApply = Seq(
      ("mffc", {sg: StatementGraph => sg.coarsenToMFFCs()}),
      ("source", {sg: StatementGraph => sg.consolidateSourceZones()}),
      ("single", {sg: StatementGraph => sg.mergeSingleInputMFFCsToParents()}),
      ("siblings", {sg: StatementGraph => sg.mergeSmallSiblings()}),
      ("small", {sg: StatementGraph => sg.mergeSmallZones(20, 0.5)}),
      ("small2", {sg: StatementGraph => sg.mergeSmallZones(40, 0.25)}),
      ("IR", {sg: StatementGraph => sg.translateBlocksIntoZones()})
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

  def getZoneOutputTypes(): Seq[(String,Type)] = {
    val allZoneOutputTypes = nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.outputTypes.toSeq
      case _ => Seq()
    }}
    allZoneOutputTypes
  }

  def getZoneNames(): Seq[String] = {
    nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Seq(az.name)
      case _ => Seq()
    }}
  }

  def analyzeZoningQuality() {
    println(s"Zones: ${getZoneNames().size}")
    val numStmtsInZones = (nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Some(az.members.size)
      case _ => None
    }}).sum
    // NOTE: Compiler withholds some statements from zoning process
    val numStmtsTotal = (nodeRefIDs map nodeSize).sum
    val percNodesInZones = 100d * numStmtsInZones / numStmtsTotal
    println(f"Nodes in zones: $numStmtsInZones/$numStmtsTotal ($percNodesInZones%2.1f%%)")
  }
}


object StatementGraph {
  def apply(bodies: Seq[Statement]) = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg
  }
}