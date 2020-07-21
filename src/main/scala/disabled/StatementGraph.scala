package disabled

import firrtl._
import firrtl.ir._
import logger._

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util
import essent.OptFlags

import collection.mutable.{ArrayBuffer, BitSet}
import java.io.{File, FileWriter}
import org.json4s._
import org.json4s.JsonDSL._
import org.json4s.native.JsonMethods._
import scala.io.Source
import scala.reflect.ClassTag


class StatementGraph extends Graph with LazyLogging {
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

  def nonEmptyStmts() = (idToStmt filter {
    s => s != EmptyStmt && !s.isInstanceOf[DefRegister] && !s.isInstanceOf[DefMemory]
  }).size

  def grabStmts(id: Int) = {
    val stmtsPossiblyWithEmpty = idToStmt(id) match {
      case b: Block => b.stmts
      case az: ActivityZone => az.memberStmts
      case s => Seq(s)
    }
    stmtsPossiblyWithEmpty filter { _ != EmptyStmt }
  }

  def allRegDefs(): Seq[DefRegister] = idToStmt collect {
    case dr: DefRegister => dr
  }

  def stateElemNames(): Seq[String] = idToStmt collect {
    case dr: DefRegister => dr.name
    case dm: DefMemory => dm.name
  }

  def containsStmtOfType[T <: Statement]()(implicit tag: ClassTag[T]): Boolean = {
    (idToStmt collectFirst { case s: T => s }).isDefined
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
      val tShadow = crawlBack(grabIDs(muxExpr.tval), dontPass ++ grabIDs(muxExpr.cond), muxID) map nameToID
      val fShadow = crawlBack(grabIDs(muxExpr.fval), dontPass ++ grabIDs(muxExpr.cond), muxID) map nameToID
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
      idToStmt(muxID) = CondMux(muxOutputName, muxExpr,
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
      if (mergeReq.size < 2) logger.info("tiny merge req!")
      val zonesStillExist = mergeReq.forall{ idToStmt(_) != EmptyStmt }
      if (zonesStillExist && safeToMergeArb(mergeReq)) {
        assert(blacklistedZoneIDs forall { !mergeReq.contains(_) })
        idToStmt(mergeReq.head) = Block(mergeReq flatMap grabStmts)
        mergeStmtsMutably(mergeReq)
      }
    }}
  }

  // NOTE: doesn't actually mutate graph, but just forecasts benefit
  def numEdgesRemovedByMerge(mergeReq: Seq[Int]): Int = {
    val totalInDegree = (mergeReq map { inNeigh(_).size }).sum
    val totalOutDegree = (mergeReq map { outNeigh(_).size }).sum
    val mergedInDegree = ((mergeReq flatMap inNeigh).distinct diff mergeReq).size
    val mergedOutDegree = ((mergeReq flatMap outNeigh).distinct diff mergeReq).size
    totalInDegree + totalOutDegree - (mergedInDegree + mergedOutDegree)
  }


  // Zoning
  //----------------------------------------------------------------------------
  val blacklistedZoneIDs = ArrayBuffer[Int]()

  def coarsenToMFFCs() {
    val startingMFFCs = initialMFFCs()
    def clumpByStmtType[T <: Statement]()(implicit tag: ClassTag[T]): Option[Int] = {
      val matchingIDs = idToStmt.zipWithIndex collect { case (t: T, id: Int) => id }
      if (matchingIDs.isEmpty) None
      else {
        val newMFFCID = matchingIDs.min
        matchingIDs foreach { startingMFFCs(_) = newMFFCID }
        Some(newMFFCID)
      }
    }
    // blacklistedZoneIDs += clumpByStmtType[RegUpdate]()
    clumpByStmtType[Print]() foreach { blacklistedZoneIDs += _ }
    val idToMFFC = findMFFCs(startingMFFCs)
    val mffcMap = Util.groupIndicesByValue(idToMFFC)
    mffcMap foreach { case (mffcID, memberIDs) => {
      if (mffcID >= 0) {
        idToStmt(mffcID) = Block(memberIDs flatMap grabStmts)
        val idsToRemove = memberIDs diff Seq(mffcID)
        mergeStmtsMutably(Seq(mffcID) ++ idsToRemove)
        assert(validNodes(mffcID))   // otherwise, MFFC incorporated exclusively invalid nodes
      }
    }}
    assert(idToMFFC forall { _ != -1 }) // all nodes reached
  }

  // TODO: respect blacklist
  def mergeSingleInputMFFCsToParents(smallZoneCutoff: Int = 20) {
    val singleInputIDs = validNodes filter {
      id => (inNeigh(id).size == 1) && (nodeSize(id) < smallZoneCutoff) && !blacklistedZoneIDs.contains(id)
    }
    val singleInputSet = singleInputIDs.toSet
    val baseSingleInputIDs = singleInputIDs filter { id => !singleInputSet.contains(inNeigh(id).head) }
    val baseIDsWithParentID = baseSingleInputIDs map { id => (id, inNeigh(id).head) }
    val basePairsWithValidParents = baseIDsWithParentID filter {
      case (id, parentID) => validNodes.contains(parentID)
    }
    if (basePairsWithValidParents.nonEmpty) {
      logger.info(s"Merging up ${basePairsWithValidParents.size} single-input zones")
      basePairsWithValidParents foreach { case (childID, parentID) => {
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
      logger.info(s"Attempting to merge ${mergesToConsider.size} groups of small siblings")
      mergeNodesSafe(mergesToConsider)
      mergeSmallSiblings(smallZoneCutoff)
    }
  }

  // merges small zones based on fraction of shared inputs
  def mergeSmallZones(smallZoneCutoff: Int = 20, mergeThreshold: Double = 0.5) {
    val smallZoneIDs = validNodes filter { id => {
      val idSize = nodeSize(id)
      idToStmt(id).isInstanceOf[Block] && (idSize > 0) && (idSize < smallZoneCutoff) && !blacklistedZoneIDs.contains(id)
    }}
    val mergesToConsider = smallZoneIDs flatMap { id => {
      val numInputs = inNeigh(id).size.toDouble
      val siblings = (inNeigh(id) flatMap outNeigh).distinct - id
      val legalSiblings = siblings filter {
        sibID => !blacklistedZoneIDs.contains(sibID) && idToStmt(sibID).isInstanceOf[Block]
      }
      val myInputSet = inNeigh(id).toSet
      val sibsScored = legalSiblings map {
        sibID => (inNeigh(sibID).count(myInputSet) / numInputs, sibID)
      }
      val choices = sibsScored filter { _._1 >= mergeThreshold }
      val choicesOrdered = choices.sortWith{_._1 > _._1}
      val topChoice = choicesOrdered.find {
        case (score, sibID) => safeToMergeArb(Seq(sibID, id))
      }
      if (topChoice.isEmpty) Seq()
      else Seq(Seq(topChoice.get._2, id))
    }}
    logger.info(s"Small zones: ${smallZoneIDs.size}")
    logger.info(s"Worthwhile merges: ${mergesToConsider.size}")
    if (mergesToConsider.nonEmpty) {
      mergeNodesSafe(mergesToConsider.toSeq)
      mergeSmallZones(smallZoneCutoff, mergeThreshold)
    }
  }

  def mergeSmallZonesDown(smallZoneCutoff: Int = 20) {
    val smallZoneIDs = validNodes filter { id => {
      val idSize = nodeSize(id)
      idToStmt(id).isInstanceOf[Block] && (idSize > 0) && (idSize < smallZoneCutoff) && !blacklistedZoneIDs.contains(id)
    }}
    val mergesToConsider = smallZoneIDs flatMap { id => {
      val mergeableChildren = outNeigh(id) filter {
        childID => safeToMergeArb(Seq(id, childID)) && !blacklistedZoneIDs.contains(childID)
      }
      if (mergeableChildren.nonEmpty) {
        val orderedByEdgesRemoved = mergeableChildren.sortBy{
          childID => numEdgesRemovedByMerge(Seq(id, childID))
        }
        val topChoice = orderedByEdgesRemoved.last
        Seq(Seq(id, topChoice))
      } else Seq()
    }}
    logger.info(s"Small zones: ${smallZoneIDs.size}")
    logger.info(s"Worthwhile merges: ${mergesToConsider.size}")
    if (mergesToConsider.nonEmpty) {
      mergeNodesSafe(mergesToConsider.toSeq)
      mergeSmallZonesDown(smallZoneCutoff)
    }
  }

  def translateBlocksIntoZones() {
    val alreadyDeclared = stateElemNames().toSet
    val blockIDs = validNodes filter { idToStmt(_).isInstanceOf[Block] }
    val idToMemberStmts: Map[Int,Seq[Statement]] = (blockIDs map {
      id => idToStmt(id) match { case b: Block => (id -> b.stmts) }
    }).toMap
    val idToProducedOutputs = idToMemberStmts mapValues { _ flatMap findResultName }
    val idToInputNames = (blockIDs map { id => {
      val zoneDepNames = idToMemberStmts(id) flatMap findDependencesStmt flatMap { _.deps }
      // FUTURE: don't call stateElemeNames repeatedly
      val externalDepNames = zoneDepNames.toSet -- (idToProducedOutputs(id).toSet -- stateElemNames)
      (id -> externalDepNames.toSeq)
    }}).toMap
    val allInputs = idToInputNames.values.flatten.toSet
    val blockIDsTopoSorted = topologicalSort filter blockIDs
    blockIDsTopoSorted.zipWithIndex foreach { case (id, index) => {
      val zoneName = id.toString
      val consumedOutputs = idToProducedOutputs(id).toSet.intersect(allInputs)
      val namesToDeclare = consumedOutputs -- alreadyDeclared
      val nameToStmts = idToMemberStmts(id) map { stmt => (findResultName(stmt) -> stmt) }
      val outputsToDeclare = nameToStmts collect {
        case (Some(name), stmt) if namesToDeclare.contains(name) => (name -> findResultType(stmt))
      }
      idToStmt(id) = ActivityZone(index, blacklistedZoneIDs.contains(id), idToInputNames(id),
                                  idToMemberStmts(id), outputsToDeclare.toMap)
    }}
  }

  def coarsenIntoZones(smallZoneCutoff: Int = 20) {
    logger.info(s"Using small-zone-cutoff of $smallZoneCutoff")
    // Not worrying about dead zones for now
    val toApply = Seq(
      ("mffc", {sg: StatementGraph => sg.coarsenToMFFCs()}),
      ("single", {sg: StatementGraph => sg.mergeSingleInputMFFCsToParents()}),
      ("siblings", {sg: StatementGraph => sg.mergeSmallSiblings()}),
      ("small", {sg: StatementGraph => sg.mergeSmallZones(smallZoneCutoff, 0.5)}),
      ("down", {sg: StatementGraph => sg.mergeSmallZonesDown(smallZoneCutoff)}),
      ("small2", {sg: StatementGraph => sg.mergeSmallZones(2*smallZoneCutoff, 0.25)}),
      ("IR", {sg: StatementGraph => sg.translateBlocksIntoZones()})
    )
    toApply foreach { case(label, func) => {
      val startTime = System.currentTimeMillis()
      func(this)
      val stopTime = System.currentTimeMillis()
      logger.info(s"[$label] took: ${stopTime - startTime}")
      logger.info(s"Down to ${nonEmptyStmts()} statement blocks")
    }}
    logger.info(zoningQualityStats())
    logger.info(mergedRegStats())
  }


  // Zone info
  //----------------------------------------------------------------------------
  def getNumZones(): Int = idToStmt count { _.isInstanceOf[ActivityZone] }

  def getZoneInputMap(): Map[String,Seq[Int]] = {
    val allZoneInputs = validNodes.toSeq flatMap { id => idToStmt(id) match {
      case az: ActivityZone if !az.alwaysActive => az.inputs map { (_, az.id) }
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
    val alreadyDeclared = stateElemNames().toSet
    val allZoneInputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.inputs
      case _ => Seq()
    }}).toSet
    val allZoneOutputs = (idToStmt flatMap { _ match {
      case az: ActivityZone => az.outputsToDeclare.keys
      case _ => Seq()
    }}).toSet ++ alreadyDeclared.toSet
    (allZoneInputs -- allZoneOutputs).toSeq
  }

  def getExternalZoneInputTypes(extIOtypes: Map[String, Type]): Seq[(String,Type)] = {
    getExternalZoneInputNames() map {
      name => (name, if (name.endsWith("reset")) UIntType(IntWidth(1)) else extIOtypes(name))
    }
  }

  def zoningQualityStats(): String = {
    val numZones = getNumZones()
    val zoneSizes = nodeRefIDs flatMap { id => idToStmt(id) match {
      case az: ActivityZone => Some(nodeSize(id))
      case _ => None
    }}
    val numStmtsInZones = zoneSizes.sum
    // NOTE: Compiler withholds some statements from zoning process
    val numStmtsTotal = (nodeRefIDs map nodeSize).sum
    val percNodesInZones = 100d * numStmtsInZones / numStmtsTotal
    val numEdgesOrig = (nodeRefIDs flatMap {
      id => grabStmts(id) flatMap {
        stmt => findDependencesStmt(stmt) map { _.deps.size }
      }
    }).sum
    val allOutputMaps = getZoneInputMap()
    val numOutputsUnique = allOutputMaps.size
    val numOutputsFlat = (allOutputMaps map { _._2.size }).sum
    val percEdgesInZones = 100d * (numEdgesOrig - numOutputsFlat) / numEdgesOrig
    f"""|Zones: $numZones
        |Output nodes: $numOutputsUnique
        |Nodes in zones: $numStmtsInZones ($percNodesInZones%2.1f%%)
        |Edges in zones: ${numEdgesOrig - numOutputsFlat} ($percEdgesInZones%2.1f%%))
        |Nodes/zone: ${numStmtsTotal.toDouble/numZones}%.1f
        |Outputs/zone: ${numOutputsUnique.toDouble/numZones}%.1f
        |Zone size range: ${zoneSizes.min} - ${zoneSizes.max}""".stripMargin
  }

  def mergedRegStats(): String = {
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
    s"With zoning, $numMergedRegs/$numRegs registers have $$next and $$final in same zone"
  }

  def dumpZoneInfoToJson(opt: OptFlags, sigNameToID: Map[String,Int], filename: String = "partStats.json") {
    val azStmts = idToStmt collect { case az: ActivityZone => az }
    def computeMemberIds(az: ActivityZone) = {
      az.memberStmts map findResultName collect {
        case Some(name) if (sigNameToID.contains(name)) => sigNameToID(name)
      }
    }
    def computeOutputIds(az: ActivityZone) = {
      val outputNames = az.outputsToDeclare map { _._1 }
      outputNames map sigNameToID
    }
    def azToJson(az: ActivityZone): JValue = {
      val baseJson = (
        ("id" -> az.id) ~
        ("size" -> flattenStmts(az).size) ~
        ("num-inputs" -> az.inputs.size) ~
        ("num-outputs" -> az.outputsToDeclare.size) ~
        ("zone-cutoff" -> opt.zoneCutoff)
      )
      // TODO: pull out zone-cutoff into overall stats
      if (sigNameToID.nonEmpty) {
        baseJson ~
        ("input-ids" -> (az.inputs filter { sigNameToID.contains } map sigNameToID)) ~
        ("member-ids" -> computeMemberIds(az)) ~
        ("output-ids" -> computeOutputIds(az))
      } else baseJson
    }
    val fw = new FileWriter(new File(filename))
    fw.write(pretty(render(azStmts map azToJson)))
    fw.close()
  }

  def extractResultOp(stmt: Statement): String = {
    val resultExpr = stmt match {
      case dn: DefNode => dn.value
      case c: Connect => c.expr
    }
    resultExpr match {
      case w: WRef => "WRef"
      case ul: UIntLiteral => "UIntLit"
      case sl: SIntLiteral => "SIntLit"
      case m: Mux => "Mux"
      case w: WSubField => "WSubField"
      case w: WSubAccess => "WSubAccess"
      case p: DoPrim => "PrimOp-" + p.op.toString
    }
  }

  def dumpNodeTypeToJson(sigNameToID: Map[String,Int], filename: String = "nodeTypes.json") {
    val coveredGraphIDs = validNodes filter { id => sigNameToID.contains(idToName(id)) }
    def graphIDtoJson(id: Int): JValue = {
      (
        ("id" -> sigNameToID(idToName(id))) ~
        ("op" -> extractResultOp(idToStmt(id)))
      )
    }
    val fw = new FileWriter(new File(filename))
    fw.write(pretty(render(coveredGraphIDs map graphIDtoJson)))
    fw.close()
  }

  def reachableAfter(sigNameToID: Map[String,Int], filename: String = "reachPost.json") {
    val azStmts = idToStmt collect { case az: ActivityZone => az }
    def findReachableInZone(az: ActivityZone): JValue = {
      val zsg = StatementGraph(az.memberStmts)
      val coveredGraphIDs = zsg.validNodes filter {
        id => sigNameToID.contains(zsg.idToName(id))
      }
      val starters = coveredGraphIDs collect {
        case id if (extractResultOp(zsg.idToStmt(id)) == "Mux") => id
        // case id if (zsg.idToStmt(id).isInstanceOf[DefRegister]) => id
        // case id if (zsg.idToStmt(id).isInstanceOf[Connect]) => id
      }
      val depthReached = ArrayBuffer.fill(zsg.numNodeRefs)(-1)
      starters foreach { id => depthReached(id) = 0 }
      zsg.reachAll(starters.toSet, 1, depthReached)
      val reached = depthReached count { _ == 1 }
      // println(s"zone ${az.id} starting from ${starters.size} reached $reached/${az.memberStmts.size - starters.size}")
      (
        ("az-id" -> az.id) ~
        ("starter_size" -> starters.size) ~
        ("reached" -> reached) ~
        ("az-size" -> az.memberStmts.size)
      )
    }
    val fw = new FileWriter(new File(filename))
    fw.write(pretty(render(azStmts map findReachableInZone)))
    fw.close()
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
      val nextExpr = idToStmt(nextID) match {
        case c: Connect => c.expr
        case dn: DefNode => dn.value
        case _ => throw new Exception("$next statement is not a Connect or DefNode")
      }
      val finalRegUpdate = idToStmt(id) match {
        case ru: RegUpdate => ru
        case _ => throw new Exception("$final statement is not a RegUpdate")
      }
      idToStmt(id) = finalRegUpdate.copy(expr = nextExpr)
      mergeStmtsMutably(Seq(id, nextID))
    }}
    logger.info(s"Was able to elide ${elidedRegIDs.size}/${regUpdateIDs.size} intermediate reg updates")
  }


  // Miscellaneous Output and Analysis
  //----------------------------------------------------------------------------
  def writeDotFileWithSizes(filename: String) {
    val fw = new FileWriter(new File(filename))
    fw.write("digraph rocketchip {\n")
      // (0 until numNodeRefs())
    validNodes foreach { rowID => {
      outNeigh(rowID) foreach { colID => {
        fw.write(s"  $rowID -> $colID;\n")
      }}
      val sizeOfNode = (nodeSize(rowID))
      // fw.write(s"  $rowID [label=$sizeOfNode];\n")
      val nodeColorBySize = if (sizeOfNode < 20) "blue"
                            else if (sizeOfNode < 50) "green"
                            else if (sizeOfNode < 200) "orange"
                            else "red"
      fw.write(s"  $rowID [color=$nodeColorBySize];\n")
    }}
    fw.write("}\n")
    fw.close()
  }
}


object StatementGraph {
  def apply(bodies: Seq[Statement]): StatementGraph = {
    val sg = new StatementGraph
    sg.buildFromBodies(bodies)
    sg.addOrderingDepsForStateUpdates()
    sg
  }

  def apply(circuit: Circuit): StatementGraph = apply(flattenWholeDesign(circuit, true))
}
