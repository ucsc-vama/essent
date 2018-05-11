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

  def translateBlocksIntoZones(alreadyDeclared: Set[String]) {
    val blockIDs = validNodes filter { idToStmt(_).isInstanceOf[Block] }
    val idToMemberStmts: Map[Int,Seq[Statement]] = (blockIDs map {
      id => idToStmt(id) match { case b: Block => (id -> b.stmts) }
    }).toMap
    val idToHEs = idToMemberStmts mapValues { members => members flatMap findDependencesStmt }
    val idToMemberNames = idToHEs mapValues { zoneHEs => zoneHEs map { _.name } }
    val idToInputNames = idToHEs map { case (id, zoneHEs) => {
      val zoneDepNames = (zoneHEs flatMap { _.deps }).distinct
      val externalDepNames = zoneDepNames diff idToMemberNames(id)
      (id -> externalDepNames)
    }}
    val inputNameToConsumingZoneIDs = Util.groupByFirst(idToInputNames.toSeq flatMap {
      case (id, inputNames) => inputNames map { (_, id) }
    })
    val cleanInputNameToConsumingZoneIDs = inputNameToConsumingZoneIDs mapValues {
      zoneIDs => zoneIDs filter { !blacklistedZoneIDs.contains(_) }
    }
    blockIDs foreach { id => {
      val zoneName = if (!blacklistedZoneIDs.contains(id)) id.toString else "always" + id
      val producedOutputs = (idToMemberStmts(id) flatMap findResultName).toSet
      val consumedOutputs = producedOutputs.intersect(cleanInputNameToConsumingZoneIDs.keys.toSet)
      val outputConsumers = consumedOutputs map { outputName => {
        val consumerIDs = cleanInputNameToConsumingZoneIDs.getOrElse(outputName, Seq())
        (outputName, consumerIDs map { _.toString })
      }}
      val decOutputNameSet = consumedOutputs -- alreadyDeclared
      val outputTypes = idToHEs(id) flatMap {
        he => if (decOutputNameSet.contains(he.name)) Seq((he.name -> findResultType(he.stmt)))
              else Seq()
      }
      val myInputs = if (!blacklistedZoneIDs.contains(id)) idToInputNames(id) else Seq()
      idToStmt(id) = ActivityZone(zoneName, myInputs, idToMemberStmts(id),
                                  idToMemberNames(id), outputConsumers.toMap, outputTypes.toMap)
    }}
  }

  def coarsenIntoZones() {
    val alreadyDeclared = idToStmt collect {
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
      ("IR", {sg: StatementGraph => sg.translateBlocksIntoZones(alreadyDeclared.toSet)})
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

  def getExternalZoneInputNames(): Seq[String] = {
    val allZoneInputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}).toSet
    val allZoneOutputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.outputConsumers.keys
      case _ => Seq()
    }}).toSet
    (allZoneInputs -- allZoneOutputs).toSeq
  }

  def getExternalZoneInputTypes(extIOtypes: Map[String, Type]): Seq[(String,Type)] = {
    getExternalZoneInputNames() map {
      name => (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
    }
  }

  // is this needed?
  def getZoneInputMap(): Map[String,Seq[String]] = {
    val allZoneInputs = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone => az.inputs map { (_, id.toString) }
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

  def printMergedRegStats() {
    val numRegs = idToStmt count { _.isInstanceOf[DefRegister] }
    val numMergedRegs = (idToStmt collect {
      case az: ActivityZone => {
        val regUpdatesInZone = az.memberStmts collect { case ru: RegUpdate => ru }
        val regUpdateNames = regUpdatesInZone map { ru: RegUpdate => emitExpr(ru.regRef) }
        val potentialNextRegNames = regUpdateNames map { _.replace('.','$') + "$next" }
        val mergedRegsInZone = potentialNextRegNames.intersect(az.memberNames)
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
    println(f"Zone size range: ${zoneSizes.min} - ${zoneSizes.max}")
  }


  // Register merging
  //----------------------------------------------------------------------------
  def mergeRegUpdatesIntoZones(regsToConsider: Seq[String]): Seq[String] = {
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
        regReaderZoneIDs filter { _ != regWriterZoneID } foreach { readerID => {
          if (!outNeigh(readerID).contains(regWriterZoneID))
            addEdge(idToName(readerID), idToName(regWriterZoneID))
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
          if (findResultName(c).get == targName + "$next") {
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


  // MemWrite merging
  //----------------------------------------------------------------------------
  // NOTE: if used, will need to add if (update_registers) to Emitter for MemWrite
  def mergeMemWritesIntoSG(memWrites: Seq[MemWrite]): Seq[MemWrite] = {
    // FUTURE: may be able to include MemWrites in body when sg is built, and just add edges later
    val unmergedMemWrites = memWrites flatMap { mw => {
      val memID = nameToID(mw.memName)
      val memReaderNames = outNeigh(memID) map idToName
      buildFromBodies(Seq(mw))
      memReaderNames foreach { readerName => addEdge(readerName, mw.nodeName) }
      Seq()
    }}
    // returns mem writes it was unable to merge (why couldn't it merge all?)
    unmergedMemWrites
  }

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