package essent

import firrtl._
import firrtl.ir._

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._

import collection.mutable.{ArrayBuffer, BitSet}
import scala.reflect.ClassTag


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
      if ((he.stmt.isInstanceOf[DefRegister]) || (he.stmt.isInstanceOf[DefMemory]))
        validNodes -= getID(he.name)
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
      val muxOutputName = findResultName(idToStmt(muxID)).get
      val (tShadow, fShadow) = muxIDToShadows(muxID)
      val muxOutputStmt = idToStmt(muxID) mapExpr replaceMux(muxExpr.tval)
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
  val blacklistedZoneIDs = ArrayBuffer[Int]()

  def coarsenToMFFCs() {
    val startingMFFCs = initialMFFCs()
    def clumpByStmtType[T <: Statement]()(implicit tag: ClassTag[T]): Int = {
      val matchingIDs = idToStmt.zipWithIndex collect { case (t: T, id: Int) => id }
      val newMFFCID = matchingIDs.min
      matchingIDs foreach { startingMFFCs(_) = newMFFCID }
      newMFFCID
    }
    // blacklistedZoneIDs += clumpByStmtType[RegUpdate]()
    blacklistedZoneIDs += clumpByStmtType[Print]()
    val idToMFFC = findMFFCs(startingMFFCs)
    val mffcMap = Util.groupIndicesByValue(idToMFFC)
    mffcMap foreach { case (mffcID, memberIDs) => {
      if (mffcID > 0) {
        idToStmt(mffcID) = Block(memberIDs flatMap grabStmts)
        val idsToRemove = memberIDs diff Seq(mffcID)
        mergeStmtsMutably(Seq(mffcID) ++ idsToRemove)
        assert(validNodes(mffcID))   // otherwise, MFFC incorporated exclusively invalid nodes
      }
    }}
    assert(idToMFFC forall { _ != -1 }) // all nodes reached
  }

  // TODO: respect blacklist
  def mergeSingleInputMFFCsToParents() {
    val singleInputIDs = validNodes filter { inNeigh(_).size == 1}
    val singleInputSet = singleInputIDs.toSet
    val baseSingleInputIDs = singleInputIDs filter { id => !singleInputSet.contains(inNeigh(id).head) }
    if (baseSingleInputIDs.nonEmpty) {
      println(s"Merging up ${baseSingleInputIDs.size} single-input zones")
      baseSingleInputIDs foreach { childID => {
        val parentID = inNeigh(childID).head
        idToStmt(parentID) = Block(grabStmts(parentID) ++ grabStmts(childID))
        mergeStmtsMutably(Seq(parentID, childID))
      }}
      mergeSingleInputMFFCsToParents()
    }
  }

  def mergeSmallSiblings(smallZoneCutoff: Int = 10) {
    val smallZoneIDs = validNodes filter { id => {
      val idSize = nodeSize(id)
      idToStmt(id).isInstanceOf[Block] && (idSize > 0) && (idSize < smallZoneCutoff) && !blacklistedZoneIDs.contains(id)
    }}
    val inputsAndIDPairs = smallZoneIDs map { id => {
      val inputsCanonicalized = inNeigh(id).toSeq.sorted
      (inputsCanonicalized, id)
    }}
    val inputsToSiblings = Util.groupByFirst(inputsAndIDPairs.toSeq)
    val mergesToConsider = inputsToSiblings.toSeq collect {
      case (inputIDs, siblingIDs) if ((siblingIDs.size > 1) && safeToMergeArb(siblingIDs)) => siblingIDs
    }
    if (mergesToConsider.nonEmpty) {
      println(s"Attempting to merge ${mergesToConsider.size} groups of small siblings")
      mergeNodesSafe(mergesToConsider)
      mergeSmallSiblings(smallZoneCutoff)
    }
  }

  // merges small zones based on fraction of shared inputs
  def mergeSmallZones(smallZoneCutoff: Int = 20, mergeThreshold: Double = 0.5) {
    val smallZoneIDs = validNodes filter { id => {
      val idSize = nodeSize(id)
      idToStmt(id).isInstanceOf[Block] && (idSize > 0) && (idSize < smallZoneCutoff)
    }}
    def overlapSize(idA: Int, idB: Int): Int = inNeigh(idA).intersect(inNeigh(idB)).size
    val mergesToConsider = smallZoneIDs flatMap { id => {
      val numInputs = inNeigh(id).size.toDouble
      val siblings = (inNeigh(id) flatMap outNeigh).distinct - id
      val legalSiblings = siblings filter { !blacklistedZoneIDs.contains(_) }
      val sibsScored = legalSiblings map {
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
      mergeNodesSafe(mergesToConsider.toSeq)
      mergeSmallZones(smallZoneCutoff, mergeThreshold)
    }
  }

  def translateBlocksIntoZones(stateElemNames: Set[String]) {
    val blockIDs = validNodes filter { idToStmt(_).isInstanceOf[Block] }
    val idToMemberStmts: Map[Int,Seq[Statement]] = (blockIDs map {
      id => idToStmt(id) match { case b: Block => (id -> b.stmts) }
    }).toMap
    val idToProducedOutputs = idToMemberStmts mapValues { _ flatMap findResultName }
    val idToHEs = idToMemberStmts mapValues { members => members flatMap findDependencesStmt }
    val idToInputNames = (blockIDs map { id => {
      val zoneDepNames = (idToHEs(id) flatMap { _.deps }).toSet
      val externalDepNames = zoneDepNames -- (idToProducedOutputs(id).toSet -- stateElemNames)
      (id -> externalDepNames.toSeq)
    }}).toMap
    val allInputs = idToInputNames.values.flatten.toSet
    blockIDs foreach { id => {
      val zoneName = id.toString
      val consumedOutputs = idToProducedOutputs(id).toSet.intersect(allInputs)
      val outputNamesToDeclare = consumedOutputs -- stateElemNames
      val outputsToDeclare = idToHEs(id) collect {
        case he if (outputNamesToDeclare.contains(he.name)) => (he.name -> findResultType(he.stmt))
      }
      idToStmt(id) = ActivityZone(zoneName, blacklistedZoneIDs.contains(id), idToInputNames(id),
                                  idToMemberStmts(id), outputsToDeclare.toMap)
    }}
  }

  def coarsenIntoZones() {
    val stateElemNames = idToStmt collect {
      case dr: DefRegister => dr.name
      case dm: DefMemory => dm.name
    }
    // Not worrying about dead zones for now
    val toApply = Seq(
      ("mffc", {sg: StatementGraph => sg.coarsenToMFFCs()}),
      // ("single", {sg: StatementGraph => sg.mergeSingleInputMFFCsToParents()}),
      ("siblings", {sg: StatementGraph => sg.mergeSmallSiblings()}),
      ("small", {sg: StatementGraph => sg.mergeSmallZones(20, 0.5)}),
      ("small2", {sg: StatementGraph => sg.mergeSmallZones(40, 0.25)}),
      ("IR", {sg: StatementGraph => sg.translateBlocksIntoZones(stateElemNames.toSet)})
    )
    toApply foreach { case(label, func) => {
      val startTime = System.currentTimeMillis()
      func(this)
      val stopTime = System.currentTimeMillis()
      println(s"[$label] took: ${stopTime - startTime}")
      println(s"Down to ${nonEmptyStmts()} statement blocks")
    }}
    analyzeZoningQuality()
    printMergedRegStats()
  }


  // Zone info
  //----------------------------------------------------------------------------
  def getZoneNames(): Seq[String] = idToStmt collect { case az: ActivityZone => az.name }

  def getZoneInputMap(): Map[String,Seq[String]] = {
    val allZoneInputs = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone if !az.alwaysActive => az.inputs map { (_, az.name) }
      case _ => Seq()
    }}
    Util.groupByFirst(allZoneInputs)
  }

  def getZoneOutputsToDeclare(): Seq[(String,Type)] = {
    val allZoneOutputTypes = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.outputsToDeclare.toSeq
      case _ => Seq()
    }}
    allZoneOutputTypes
  }

  def getExternalZoneInputNames(): Seq[String] = {
    val stateElemNames = idToStmt collect {
      case dr: DefRegister => dr.name
      case dm: DefMemory => dm.name
    }
    val allZoneInputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}).toSet
    val allZoneOutputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.outputsToDeclare.keys
      case _ => Seq()
    }}).toSet ++ stateElemNames.toSet
    // FUTURE: safe to assume zones produce all state elements?
    (allZoneInputs -- allZoneOutputs).toSeq
  }

  def getExternalZoneInputTypes(extIOtypes: Map[String, Type]): Seq[(String,Type)] = {
    getExternalZoneInputNames() map {
      name => (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
    }
  }

  def printMergedRegStats() {
    val numRegs = idToStmt count { _.isInstanceOf[DefRegister] }
    val numMergedRegs = (idToStmt collect {
      case az: ActivityZone => {
        val regUpdateNames = az.memberStmts collect { case ru: RegUpdate => emitExpr(ru.regRef) }
        val potentialNextRegNames = regUpdateNames map { _.replace('.','$') + "$next" }
        val internalOutputs = az.memberStmts flatMap findResultName
        val mergedRegsInZone = potentialNextRegNames.intersect(internalOutputs)
        mergedRegsInZone.size
      }
    }).sum
    println(s"With zoning, $numMergedRegs/$numRegs registers have $$next and $$final in same zone")
  }

  def analyzeZoningQuality() {
    val numZones = getZoneNames().size
    println(s"Zones: $numZones")
    val zoneSizes = nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Some(az.memberStmts.size)
      case _ => None
    }}
    val numStmtsInZones = zoneSizes.sum
    // NOTE: Compiler withholds some statements from zoning process
    val numStmtsTotal = (nodeRefIDs map nodeSize).sum
    val percNodesInZones = 100d * numStmtsInZones / numStmtsTotal
    println(f"Nodes in zones: $numStmtsInZones ($percNodesInZones%2.1f%%)")
    val numEdgesOrig = (nodeRefIDs flatMap {
      id => grabStmts(id) flatMap {
        stmt => findDependencesStmt(stmt) map { _.deps.size }
      }
    }).sum
    val allOutputMaps = getZoneInputMap()
    val numOutputsUnique = allOutputMaps.size
    val numOutputsFlat = (allOutputMaps map { _._2.size }).sum
    val percEdgesInZones = 100d * (numEdgesOrig - numOutputsFlat) / numEdgesOrig
    println(f"Edges in zones: ${numEdgesOrig - numOutputsFlat} ($percEdgesInZones%2.1f%%)")
    println(f"Nodes/zone: ${numStmtsTotal.toDouble/numZones}%.1f")
    println(f"Outputs/zone: ${numOutputsUnique.toDouble/numZones}%.1f")
    println(f"Zone size range: ${zoneSizes.min} - ${zoneSizes.max}")
  }


  // Mutations for State Elements
  //----------------------------------------------------------------------------
  def addOrderingDepsForStateUpdates() {
    def addOrderingEdges(writerName: String, readerTarget: String) {
      if (nameToID.contains(readerTarget)) {
        val readerNames = outNeigh(nameToID(readerTarget)) map idToName
        readerNames foreach { readerName => if (readerName != writerName) addEdgeIfNew(readerName, writerName) }
      }
    }
    idToStmt foreach { stmt => stmt match {
      case ru: RegUpdate => {
        val regName = emitExpr(ru.regRef)
        addOrderingEdges(regName + "$final", regName)
      }
      case mw: MemWrite => addOrderingEdges(mw.nodeName, mw.memName)
      case _ =>
    }}
  }

  def elideIntermediateRegUpdates() {
    def safeToMergeWithParentNextNode(id: Int): Boolean = {
      (inNeigh(id).nonEmpty) &&                              // node id isn't floating (parentless)
      (idToName(inNeigh(id).head).endsWith("$next")) &&      // first parent assigns $next
      safeToMerge(idToName(id), idToName(inNeigh(id).head))  // no external paths between them
    }
    val regUpdateIDs = idToStmt.zipWithIndex collect { case (ru: RegUpdate, id: Int) => id }
    // WARNING: following filter will have side-effects on StatementGraph
    val elidedRegIDs = regUpdateIDs collect { case id if (safeToMergeWithParentNextNode(id)) => {
      val nextID = inNeigh(id).head
      val nextConnect = idToStmt(nextID) match {
        case c: Connect => c
        case _ => throw new Exception("$next statement is not a Connect")
      }
      val finalRegUpdate = idToStmt(id) match {
        case ru: RegUpdate => ru
        case _ => throw new Exception("$final statement is not a RegUpdate")
      }
      idToStmt(id) = finalRegUpdate.copy(expr = nextConnect.expr)
      mergeStmtsMutably(Seq(id, nextID))
    }}
    println(s"Was able to elide ${elidedRegIDs.size}/${regUpdateIDs.size} intermediate reg updates")
  }
}


object StatementGraph {
  def apply(bodies: Seq[Statement]) = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg.addOrderingDepsForStateUpdates()
    sg
  }
}