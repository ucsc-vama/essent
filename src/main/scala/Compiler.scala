package essent

import java.io.{File, FileWriter, Writer}
import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import essent.DedupWorker._
import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency
import firrtl.stage.transforms
import firrtl.transforms.DedupedResult
import _root_.logger._
import essent.Graph.NodeID

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer


class EssentEmitter(initialOpt: OptFlags, w: Writer, circuit: Circuit) extends LazyLogging {
  val flagVarName = "PARTflags"
  val outsideCircuitDataStructTypeName = "OutsideCircuitData"
  val dedupCircuitDataStructTypeName = "DedupCircuitData"
  val dedupCitcuitDSInstName = "dedupData"
  var dedupPlaceHolderFlagIdx = -1

  implicit var rn = new Renamer
  val actTrac = new ActivityTracker(w, initialOpt)
  val vcd = if (initialOpt.withVCD) Some(new Vcd(circuit,initialOpt,w,rn)) else None
  // Declaring Modules
  //----------------------------------------------------------------------------
  def declareModule(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regName = d.name
      Seq(s"$typeStr $regName;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${m.name}[${m.depth}];"
    }}
    val modulesAndPrefixes = findModuleInstances(m.body)
    val moduleDecs = modulesAndPrefixes map { case (module, fullName) => {
      val instanceName = fullName.split("\\.").last
      s"$module $instanceName;"
    }}
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, registerDecs)
    w.writeLines(1, memDecs)
    w.writeLines(1, m.ports flatMap emitPort(modName == topName))
    w.writeLines(1, moduleDecs)
    w.writeLines(0, "")
    w.writeLines(1, s"$modName() {")
    w.writeLines(2, initializeVals(modName == topName)(m, registers, memories))
    w.writeLines(1, "}")
    if (modName == topName) {
      w.writeLines(0, "")
      // w.writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
    } else {
      w.writeLines(0, s"} $modName;")
    }
  }

  def declareExtModule(m: ExtModule) {
    val modName = m.name
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $modName {")
    w.writeLines(1, m.ports flatMap emitPort(true))
    w.writeLines(0, s"} $modName;")
  }


  // Write General-purpose Eval
  //----------------------------------------------------------------------------
  // TODO: move specialized CondMux emitter elsewhere?
  def writeBodyInner(indentLevel: Int, sg: StatementGraph, opt: OptFlags,
                     keepAvail: Set[String] = Set()) {
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          w.writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        w.writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), opt)
        w.writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), opt)
        w.writeLines(indentLevel, "}")
      }
      case _ => {
        w.writeLines(indentLevel, emitStmt(stmt))
        if (opt.withVCD)  vcd.get.compSmallEval(stmt, indentLevel)
        if (opt.trackSigs) actTrac.emitSigTracker(stmt, indentLevel)
      }
    }}
  }

  def checkRegResetSafety(sg: StatementGraph) {
    val updatesWithResets = sg.allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    assert(updatesWithResets.isEmpty)
  }


  // Write Zoning Optimized Eval
  //----------------------------------------------------------------------------
  def genEvalFuncName(partID: Int): String = "EVAL_" + partID

  def genDepPartTriggers(consumerIDs: Seq[Int], condition: String): Seq[String] = {
    consumerIDs.sorted map { consumerID => s"$flagVarName[$consumerID] |= $condition;" }
  }

  def genAllTriggers(signalNames: Seq[String], outputConsumers: Map[String, Seq[Int]],
                     suffix: String): Seq[String] = {
    selectFromMap(signalNames, outputConsumers).toSeq flatMap { case (name, consumerIDs) => {
      genDepPartTriggers(consumerIDs, s"${rn.emit(name)} != ${rn.emit(name + suffix)}")
    }}
  }


  def getPartAliasGlobalName(pardId: Int) = s"PARTAlias_${pardId}"
  val partAliasArrayName = "partAlias"
  val currentCPPartAlias = mutable.ArrayBuffer[NodeID]()

  def genDepPartTriggersForDedup(consumerIDs: Seq[Int], condition: String): Seq[String] = {
    consumerIDs.sorted map { consumerID => {
      val partAliasOffset = currentCPPartAlias.size
      currentCPPartAlias += consumerID
      s"$flagVarName[${partAliasArrayName}[${partAliasOffset}]] |= $condition;"
    }}
  }

  def genSigConsumerList(outputRealConsumers: Seq[Int], maxConsumers: Int) = {
    assert(outputRealConsumers.size <= maxConsumers)
    (outputRealConsumers ++ Seq.fill(maxConsumers)(dedupPlaceHolderFlagIdx)).take(maxConsumers)
  }

  def genAllTriggersForDedup(
                            instName: String,
                            cacheNames: Set[String],
                            ruNames: Set[String],
                            mws: Seq[MemWrite],
                            outputConsumeMap: Map[String, Seq[Int]],
                            signalMaxConsumers: mutable.LinkedHashMap[String, Int],
                            cacheSuffix: String,
                            ruSuffix: String
                          ) = {
    val mwNames = mws.map(_.memName).toSet
    // Note: A memory may have multiple writers
    val mwNameToStmts = mutable.HashMap[String, Seq[MemWrite]]()
    mws.foreach{mw => {
      val memName = mw.memName
      mwNameToStmts(memName) = mwNameToStmts.getOrElse(memName, Seq()) ++ Seq(mw)
    }}
    val allSignalNames = (cacheNames ++ ruNames ++ mwNames).map(_.stripPrefix(instName))
    assert(allSignalNames.size == signalMaxConsumers.size)
    assert(allSignalNames.diff(signalMaxConsumers.keySet).isEmpty)

    signalMaxConsumers.flatMap{case (sigShortName, maxConsumers) => {
      val canonicalName = instName + sigShortName
      val consumers = outputConsumeMap.getOrElse(canonicalName, Seq())
      assert(consumers.size <= maxConsumers)
      val consumerIDs = genSigConsumerList(consumers, maxConsumers)
      if (cacheNames.contains(canonicalName)) {
        genDepPartTriggersForDedup(consumerIDs, s"${rn.emit(canonicalName)} != ${rn.emit(canonicalName + cacheSuffix)}")
      } else if (ruNames.contains(canonicalName)) {
        genDepPartTriggersForDedup(consumerIDs, s"${rn.emit(canonicalName)} != ${rn.emit(canonicalName + ruSuffix)}")
      } else {
        assert(mwNames.contains(canonicalName))

        val mws = mwNameToStmts(canonicalName)
        mws.flatMap{mw => {
          val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
          genDepPartTriggersForDedup(consumerIDs, condition)
        }}
      }
    }}
  }

  def writeZoningPredecs(
                          sg: StatementGraph,
                          condPartWorker: MakeCondPart,
                          topName: String,
                          extIOtypes: Map[String, Type],
                          opt: OptFlags) {
    // predeclare part outputs
    val outputPairs = condPartWorker.getPartOutputsToDeclare()
    val outputConsumers = condPartWorker.getPartInputMap()
    w.writeLines(1, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name)};"})
    val extIOCacheDecs = condPartWorker.getExternalPartInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)};"
    }
    w.writeLines(1, extIOCacheDecs)
    w.writeLines(1, s"std::array<bool,${condPartWorker.getNumParts()}> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    w.writeLines(1, s"bool sim_cached = false;")
    w.writeLines(1, s"bool regs_set = false;")
    w.writeLines(1, s"bool update_registers;")
    w.writeLines(1, s"bool done_reset;")
    w.writeLines(1, s"bool verbose;")
    w.writeLines(0, "")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        w.writeLines(1, s"void ${genEvalFuncName(cp.id)}() {")
        if (!cp.alwaysActive)
          w.writeLines(2, s"$flagVarName[${cp.id}] = false;")
        if (opt.trackParts)
          w.writeLines(2, s"${actTrac.actVarName}[${cp.id}]++;")

        val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
          }}
        w.writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
        val bodySG = StatementGraph(noRegUpdates)
        if (opt.conditionalMuxes)
          MakeCondMux(bodySG, rn, keepAvail)
        writeBodyInner(2, bodySG, opt, keepAvail)
        w.writeLines(2, genAllTriggers(cp.outputsToDeclare.keys.toSeq, outputConsumers, condPartWorker.cacheSuffix))
        val regUpdateNamesInPart = regUpdates flatMap findResultName
        w.writeLines(2, genAllTriggers(regUpdateNamesInPart, outputConsumers, "$next"))
        // triggers for MemWrites
        val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }
        val memWriteTriggers = memWritesInPart flatMap { mw => {
          val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
          genDepPartTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
        }}
        w.writeLines(2, memWriteTriggers)
        w.writeLines(2, regUpdates flatMap emitStmt)

        w.writeLines(1, "}")
      }
      case _ => throw new Exception(s"Statement at top-level is not a CondPart (${stmt.serialize})")
    }}
    w.writeLines(0, "")
  }


  def genPartAliasDecls(cpId: Int) = {
    s"const int ${getPartAliasGlobalName(cpId)}[${currentCPPartAlias.size}] = { ${currentCPPartAlias.mkString(", ")} };"
  }


  def writeZoningPredecsForDedup(
                          sg: StatementGraph,
                          condPartWorker: MakeCondPart,
                          topName: String,
                          extIOtypes: Map[String, Type],
                          opt: OptFlags,
                          dedupInfo: DedupCPInfo) {
    // predeclare part outputs
    val outputPairs = condPartWorker.getPartOutputsToDeclare().filterNot{case (sigName, sigType) => dedupInfo.allDedupInstRWSignals.contains(sigName)}
    val outputConsumers = condPartWorker.getPartInputMap()
    w.writeLines(1, "// Cached signals")
    w.writeLines(1, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name)};"})
    w.writeLines(1, "// Done cached signals")
    val extIOCacheDecs = condPartWorker.getExternalPartInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)};"
    }
    w.writeLines(1, extIOCacheDecs)
    w.writeLines(1, s"// ${condPartWorker.getNumParts()} parts in total. The last bit is used by dedup (not any part)")
    w.writeLines(1, s"std::array<bool,${condPartWorker.getNumParts() + 1}> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    w.writeLines(1, s"bool sim_cached = false;")
    w.writeLines(1, s"bool regs_set = false;")
    w.writeLines(1, s"bool update_registers;")
    w.writeLines(1, s"bool done_reset;")
    w.writeLines(1, s"bool verbose;")
    w.writeLines(0, "")

    dedupPlaceHolderFlagIdx = condPartWorker.getNumParts()
    val orderedSG = sg.stmtsOrdered()

    val cpidToCPStmt = orderedSG.map{case cp:CondPart => cp.id -> cp}.toMap

    val dedupMainInstCPs = cpidToCPStmt.filter{case (cpid, cp) => dedupInfo.dedupCPIdMap.contains(cpid)}.toSeq.sortBy(_._1)
    val dedupOtherInstCPs = cpidToCPStmt.filter{case (cpid, cp) => dedupInfo.allDedupCPids.contains(cpid) && (!dedupInfo.dedupCPIdMap.contains(cpid))}.toSeq.sortBy(_._1)


    // TODO: this is used for debug purpose
    val cpOutputTriggerCount = mutable.HashMap[Int, Int]()

    // collect max activated parts for each signal
    val cpOutputMaxConsumers = dedupInfo.dedupCPIdMap.map{case (mainId, otherIds) => {
      val pairedCPs = (Seq(mainId) ++ otherIds).map(cpidToCPStmt)
      // Keep order
      val signalMaxConsumers = mutable.LinkedHashMap[String, Int]()

      pairedCPs.foreach{cp => {
        val instName = dedupInfo.cpIdToDedupInstName(cp.id)

        val partCacheTriggers = cp.outputsToDeclare.keys.toSeq
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val ruTriggers = regUpdates flatMap findResultName
        val mwTriggers = cp.memberStmts collect { case mw: MemWrite => mw } map {mw => mw.memName}

        (partCacheTriggers ++ ruTriggers ++ mwTriggers).foreach{sigName => {
          val dedupName = sigName.stripPrefix(instName)
          assert(sigName != dedupName)
          val consumerCnt = outputConsumers.getOrElse(sigName, Seq()).size

          val oldConsumerCnt = signalMaxConsumers.getOrElse(dedupName, 0)
          signalMaxConsumers(dedupName) = Seq(oldConsumerCnt, consumerCnt).max
        }}
      }}

      mainId -> signalMaxConsumers
    }}



    // Outside circuit and dedup circuit require different renamer
    val backupRn = Renamer(rn)
    rn.factorNameForDedupCircuit(sg, dedupInfo)

    // Write main dedup code
    dedupMainInstCPs.zipWithIndex.foreach{ case ((cpid, cp), cpNo) => {
      currentCPPartAlias.clear()
      currentCPPartAlias += cp.id

      w.writeLines(1, s"// Code for CondPart ${cpid}, instance name ${dedupInfo.dedupMainInstanceName}")
      (1 until dedupInfo.dedupInstanceNameList.size).foreach {idx =>{
        val correspondingCPid = dedupInfo.dedupCPIdMap(cpid)(idx - 1)
        val correspondingCPName = dedupInfo.dedupInstanceNameList(idx)
        w.writeLines(1, s"// Alias with CP ${correspondingCPid} in instance ${correspondingCPName}")
      }}

      w.writeLines(1, s"void ${genEvalFuncName(cp.id)}(${dedupCircuitDataStructTypeName}* ${dedupCitcuitDSInstName}, const int* ${partAliasArrayName}) {")
      assert(!cp.alwaysActive) // May be true in future?
      w.writeLines(2, s"${flagVarName}[${partAliasArrayName}[0]] = false;")


      if (opt.trackParts)
        w.writeLines(2, s"${actTrac.actVarName}[realPartId]++;")

      val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
        case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
      w.writeLines(2, cacheOldOutputs)
      val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
      val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
      val bodySG = StatementGraph(noRegUpdates)
      if (opt.conditionalMuxes)
        MakeCondMux(bodySG, rn, keepAvail)
      writeBodyInner(2, bodySG, opt, keepAvail)


      val regUpdateNamesInPart = regUpdates flatMap findResultName
      val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }

      val allTriggers = genAllTriggersForDedup(
        dedupInfo.dedupMainInstanceName,
        cp.outputsToDeclare.keys.toSet,
        regUpdateNamesInPart.toSet,
        memWritesInPart,
        outputConsumers,
        cpOutputMaxConsumers(cpid),
        condPartWorker.cacheSuffix,
        "$next"
      )
      w.writeLines(2, allTriggers.toSeq)

      w.writeLines(2, "// Start regUpdates")
      w.writeLines(2, regUpdates flatMap emitStmt)
      w.writeLines(2, "// End regUpdates")

      w.writeLines(1, "}")

      w.writeLines(1, genPartAliasDecls(cp.id))
      cpOutputTriggerCount(cp.id) = currentCPPartAlias.size - 1
      w.writeLines(0, "")
    }}


    // declare for replicated CP
    dedupOtherInstCPs.zipWithIndex.foreach{case ((cpid, cp), cpNo) => {
      val correspondingMainCPId = dedupInfo.dedupOtherCPToMainCPMap(cpid)
      val instName = dedupInfo.cpIdToDedupInstName(cpid)
      w.writeLines(1, s"// CondPart ${cpid} skipped as it's dedupped (Alias of CondPart ${correspondingMainCPId})")

      currentCPPartAlias.clear()
      currentCPPartAlias += cp.id

      // Assertions
      val correspondingCP = cpidToCPStmt(correspondingMainCPId)
      assert(cp.outputsToDeclare.size == correspondingCP.outputsToDeclare.size)


//      w.writeLines(1, "/*")
      val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
      val regUpdateNamesInPart = regUpdates flatMap findResultName
      val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }

      val allTriggers = genAllTriggersForDedup(
        instName,
        cp.outputsToDeclare.keys.toSet,
        regUpdateNamesInPart.toSet,
        memWritesInPart,
        outputConsumers,
        cpOutputMaxConsumers(correspondingMainCPId),
        condPartWorker.cacheSuffix,
        "$next"
      )
//      w.writeLines(2, allTriggers.toSeq)
//      w.writeLines(1, "*/")

      w.writeLines(1, genPartAliasDecls(cp.id))

      cpOutputTriggerCount(cp.id) = currentCPPartAlias.size - 1
      w.writeLines(0, "")

    }}

    rn = Renamer(backupRn)
    rn.factorNameForOutsideCircuit(sg, dedupInfo)

    // declare for remaining CP
    val allCPs = orderedSG.collect{case cp: CondPart => cp}
    allCPs.filter{cp => !dedupInfo.allDedupCPids.contains(cp.id)}.foreach{ cp => {
      w.writeLines(1, s"void ${genEvalFuncName(cp.id)}() {")
      if (!cp.alwaysActive)
        w.writeLines(2, s"$flagVarName[${cp.id}] = false;")
      if (opt.trackParts)
        w.writeLines(2, s"${actTrac.actVarName}[${cp.id}]++;")

      val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
        case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
      w.writeLines(2, cacheOldOutputs)
      val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
      val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
      val bodySG = StatementGraph(noRegUpdates)
      if (opt.conditionalMuxes)
        MakeCondMux(bodySG, rn, keepAvail)
      writeBodyInner(2, bodySG, opt, keepAvail)
      w.writeLines(2, genAllTriggers(cp.outputsToDeclare.keys.toSeq, outputConsumers, condPartWorker.cacheSuffix))
      val regUpdateNamesInPart = regUpdates flatMap findResultName
      w.writeLines(2, genAllTriggers(regUpdateNamesInPart, outputConsumers, "$next"))
      // triggers for MemWrites
      val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }
      val memWriteTriggers = memWritesInPart flatMap { mw => {
        val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
        genDepPartTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
      }}
      w.writeLines(2, memWriteTriggers)
      w.writeLines(2, regUpdates flatMap emitStmt)

      w.writeLines(1, "}")
    }}
    w.writeLines(0, "")

    if (opt.genRegDump) writeRegisterDump(sg, rn)
  }

  def writeZoningBody(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags) {
    w.writeLines(2, "if (reset || !done_reset) {")
    w.writeLines(3, "sim_cached = false;")
    w.writeLines(3, "regs_set = false;")
    w.writeLines(2, "}")
    w.writeLines(2, "if (!sim_cached) {")
    w.writeLines(3, s"$flagVarName.fill(true);")
    w.writeLines(2, "}")
    w.writeLines(2, "sim_cached = regs_set;")
    w.writeLines(2, "this->update_registers = update_registers;")
    w.writeLines(2, "this->done_reset = done_reset;")
    w.writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    w.writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    w.writeLines(2, extIOCaches.toSeq)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        if (!cp.alwaysActive)
          w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
        else
          w.writeLines(2, s"${genEvalFuncName(cp.id)}();")
      }
      case _ => w.writeLines(2, emitStmt(stmt))
    }}
    // w.writeLines(2,  "#ifdef ALL_ON")
    // w.writeLines(2, s"$flagVarName.fill(true);" )
    // w.writeLines(2,  "#endif")
    w.writeLines(2, "regs_set = true;")
  }

  def writeZoningBodyForDedup(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags, dedupInfo: DedupCPInfo) {
    w.writeLines(2, "if (reset || !done_reset) {")
    w.writeLines(3, "sim_cached = false;")
    w.writeLines(3, "regs_set = false;")
    w.writeLines(2, "}")
    w.writeLines(2, "if (!sim_cached) {")
    w.writeLines(3, s"$flagVarName.fill(true);")
    w.writeLines(2, "}")
    w.writeLines(2, "sim_cached = regs_set;")
    w.writeLines(2, "this->update_registers = update_registers;")
    w.writeLines(2, "this->done_reset = done_reset;")
    w.writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    w.writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    w.writeLines(2, extIOCaches.toSeq)

    val orderedSG = sg.collectValidStmts(TopologicalSortWithLocality(sg, dedupInfo.dedupMergeIDMap.map{case (main, others) => Seq(main) ++ others}.toSeq))
    orderedSG foreach {
      case cp: CondPart => {
        if (cp.alwaysActive)
          w.writeLines(2, s"${genEvalFuncName(cp.id)}();")
        else {
          if (dedupInfo.allDedupCPids.contains(cp.id)) {
            val partAliasName = getPartAliasGlobalName(cp.id)
            if (dedupInfo.dedupCPIdMap.contains(cp.id)) {
              // main inst cps
              val funcCall = s"${genEvalFuncName(cp.id)}(&${rn.getDedupInstanceDSName(0)}, ${partAliasName})"
              w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${funcCall};")
            } else {
              // other deduplicated instances
              val correspondingCPId = dedupInfo.dedupOtherCPToMainCPMap(cp.id)
              val instName = dedupInfo.cpIdToDedupInstName(cp.id)
              val instId = dedupInfo.dedupInstanceNameToId(instName)
              w.writeLines(2, s"// CondPart ${cp.id} in [${instName}] is an alias of CondPart ${correspondingCPId} in instance ${dedupInfo.dedupMainInstanceName}")
              val funcCall = s"${genEvalFuncName(correspondingCPId)}(&${rn.getDedupInstanceDSName(instId)}, ${partAliasName})"
              w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${funcCall};")
            }
          } else {
            // Regular
            w.writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
          }
        }
      }
      case stmt => w.writeLines(2, emitStmt(stmt))
    }
    // w.writeLines(2,  "#ifdef ALL_ON")
    // w.writeLines(2, s"$flagVarName.fill(true);" )
    // w.writeLines(2,  "#endif")
    w.writeLines(2, "regs_set = true;")
  }


  def writeFlatternVariableDeclaration(regDecls: Seq[(String, String)], memDecls: Seq[(String, String, BigInt, BigInt)], memPtrs: Seq[(String, String)]) = {

    w.writeLines(1, "// Registers")
    regDecls.foreach{case (typeStr, declName) => {
      w.writeLines(1, s"${typeStr} ${declName};")
    }}

    if (memDecls.nonEmpty) {
      w.writeLines(1, "// Memories")
      memDecls.foreach { case (typeStr, declName, memDepth, memWidth) => {
        w.writeLines(1, s"${typeStr} ${declName}[${memDepth}];")
      }}
    }

    if (memPtrs.nonEmpty) {
      w.writeLines(1, "// Memory pointers")
      memPtrs.foreach { case (declName, typeStr) => {
        w.writeLines(1, s"${typeStr}* ${declName};")
      }}
    }

    w.writeLines(0, "")
    w.writeLines(1, s"void init() {")
    w.writeLines(2, "// Rand init registers")
    regDecls.foreach{case (typeStr, declName) => {
      w.writeLines(2, s"${declName}.rand_init();")
    }}
    w.writeLines(0, "")

    w.writeLines(2, "// Set all pointers (if any) to nullptr")
    memPtrs.foreach{case (declName, typrStr) => {
      w.writeLines(2, s"${declName} = nullptr;")
    }}
    w.writeLines(0, "")

    w.writeLines(2, "// Initialize all memories")
    memDecls.foreach{case (typeStr, declName, memDepth, memWidth) => {
      // TODO: Is this magic number reasonable? Need performance data
      val initStmts = if ((memDepth > 1000) && (memWidth) <= 64) {
        Seq(s"${declName}[0].rand_init();",
          s"for (size_t a=0; a < ${memDepth}; a++) ${declName}[a] = ${declName}[0].as_single_word() + a;")
      } else {
        Seq(s"for (size_t a=0; a < ${memDepth}; a++) ${declName}[a].rand_init();")
      }
      w.writeLines(2, initStmts)
    }}
    w. writeLines(1, "}")

  }

  def writeRegisterDump(sg: StatementGraph, rn: Renamer) = {

    // Registers
    val cpTopoOrdered = TopologicalSort(sg).filter(sg.validNodes.contains)
    val sgTopoOrdered = cpTopoOrdered.flatMap{id => {
      sg.idToStmt(id) match {
        case cp: CondPart => cp.memberStmts
        case _ => Seq()
      }
    }}

    val allWriteRegisterNamesSorted = sgTopoOrdered.collect { case ru: RegUpdate => ru}.map{ru => emitExpr(ru.regRef)}.sorted

    w.writeLines(1, s"void dumpRegisterNames(std::ofstream& ofs) {")
    w.writeLines(2, "ofs << ")
    allWriteRegisterNamesSorted.foreach{regName => {
      val regDeclName = rn.emit(regName)
      w.writeLines(3, s""""${regName}, ${regDeclName}\\n"""")
    }}
    w.writeLines(2, ";")
    w.writeLines(1, "}")


    w.writeLines(1, s"void dumpRegisterContent(std::ofstream& ofs) {")
    allWriteRegisterNamesSorted.foreach{regName => {
      val regDeclName = rn.emit(regName)
      w.writeLines(2, s"""ofs << ${regDeclName} << "\\n";""")
    }}
    w.writeLines(1, "}")
  }

  def declareFlattenModules(sg:StatementGraph, dedupInfo: DedupCPInfo): Unit = {
    val topName = circuit.main
    val topModule = findModule(topName, circuit) match {case m: Module => m}

    val modules = circuit.modules.collect {case m: Module => m}
    val extModules = circuit.modules.collect {case em: ExtModule => em}
    val moduleDict = modules.map(x => (x.name, x)).toMap
    val extModuleDict = extModules.map(x => (x.name, x)).toMap

    val modulesAndPrefixes = findAllModuleInstances(circuit)
    // Don't collect extmodules
    val regularModulesAndPrefixes = modulesAndPrefixes filter {case (modName, _) => moduleDict.contains(modName)}
    val extModulesAndPrefixes = modulesAndPrefixes.filter{case(modName, _) => {extModuleDict.contains(modName)}}

    val dedupRegisters = (dedupInfo.dedupRegisterNames).toSet
    val mainInstRegisters = (dedupInfo.dedupMainRegisterNames).toSet
    val mainInstName = dedupInfo.dedupMainInstanceName

//    // Registers
//    val cpTopoOrdered = TopologicalSort(sg).filter(sg.validNodes.contains)
//    val sgTopoOrdered = cpTopoOrdered.flatMap{id => {
//      sg.idToStmt(id) match {
//        case cp: CondPart => {
//          cp.memberStmts
//        }
//      }
//    }}

    val allRegisterNames = dedupInfo.allRegisterNames

    // (typeStr, declName)
    val outsideRegisterDecls = ArrayBuffer[(String, String)]()
    val dedupRegisterDecls = ArrayBuffer[(String, String)]()

    allRegisterNames.foreach{canonicalName => {
      val typeStr = dedupInfo.allRegesterNameToTypeStr(canonicalName)
      if (!dedupRegisters.contains(canonicalName)) {
        val genName = removeDots(canonicalName)
        val decl = (typeStr, genName)
        outsideRegisterDecls.append(decl)
      }
      if (mainInstRegisters.contains(canonicalName)) {
        val shortName = canonicalName.stripPrefix(mainInstName)
        val genName = removeDots(shortName)
        val decl = (typeStr, genName)
        dedupRegisterDecls.append(decl)
      }
    }}



    // (typeStr, declName, depth, width)
    val allMemoryDecls = regularModulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories map {m: DefMemory => {
        val canonicalName = prefix + m.name
        val declName = removeDots(canonicalName)
        (genCppType(m.dataType), declName, m.depth, bitWidth(m.dataType))
      }}
    }}


    // Memory pointers
    val allMemoryNameAndType = regularModulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories map {m: DefMemory => {
        (prefix + m.name -> m.dataType)
      }}
    }}.toMap


    val allAccessedMemNamesOrdered = dedupInfo.allMemoryNamesOrdered.filter(dedupInfo.dedupAccessedMemoryByInst(dedupInfo.dedupMainInstanceName).contains)
    assert(allAccessedMemNamesOrdered.size == dedupInfo.dedupAccessedMemoryByInst(dedupInfo.dedupMainInstanceName).size)
    val dedupAccessedMemoryInfo = allAccessedMemNamesOrdered.map{memName => {
      val declName = removeDots(memName.stripPrefix(dedupInfo.dedupMainInstanceName))
      (declName, genCppType(allMemoryNameAndType(memName)))
    }}

    // Declare global data for outside circuit and all memories
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct ${outsideCircuitDataStructTypeName} {")
    w.writeLines(0, "")
    writeFlatternVariableDeclaration(outsideRegisterDecls, allMemoryDecls, Seq())
    w. writeLines(0, s"} $outsideCircuitDataStructTypeName;")


    // Declare dedup data
    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct ${dedupCircuitDataStructTypeName} {")
    w.writeLines(0, "")
    writeFlatternVariableDeclaration(dedupRegisterDecls, Seq(), dedupAccessedMemoryInfo)

    // 4. stmtSorted -> filter output -> depName
    val cachedSignalsOrdered = dedupInfo.allCPOutputSignalsTopoSorted_R
    val dedupInstInternalCachedSignals = dedupInfo.mainDedupInstInternalSignals.diff(dedupRegisters)

    val dedupInstBoundaryCachedSignals = dedupInfo.mainDedupInstBoundarySignals.diff(dedupInfo.allRegisterNameSet).diff(dedupInfo.allMemoryNameSet)
    val dedupInstCachedSignals = dedupInstInternalCachedSignals ++ dedupInstBoundaryCachedSignals

    // Assertion: Cached signal can either be internal or boundary, not both
    assert(dedupInstInternalCachedSignals.size + dedupInstBoundaryCachedSignals.size == dedupInstCachedSignals.size)

    val dedupInstCacheSignalsOrdered = cachedSignalsOrdered.filter(dedupInstCachedSignals.contains)
    assert(dedupInstCacheSignalsOrdered.size == dedupInstCachedSignals.size)

    w.writeLines(1, "// Declare cached signals (Both internal signals and boundary signals)")
    dedupInstCacheSignalsOrdered.foreach{ sigName =>
      val sigType = dedupInfo.signalNameToType(sigName)

      val typeStr = genCppType(sigType)
      val declName = removeDots(sigName.stripPrefix(dedupInfo.dedupMainInstanceName))
      w.writeLines(1, s"${typeStr} ${declName};")
    }


    w. writeLines(0, s"} $dedupCircuitDataStructTypeName;")
    w.writeLines(0, "")



    w.writeLines(0, "")
    w.writeLines(0, s"typedef struct $topName {")
    w.writeLines(0, "")



    // Declare top Module signals
    val topModuleRegisters = findInstancesOf[DefRegister](topModule.body)
    val topModuleMemories = findInstancesOf[DefMemory](topModule.body)
    val topModuleRegDesc = topModuleRegisters flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regName = d.name
      Seq(s"$typeStr $regName;")
    }}
    val topModuleMemDesc = topModuleMemories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${m.name}[${m.depth}];"
    }}
    w.writeLines(1, topModuleRegDesc)
    w.writeLines(1, topModuleMemDesc)
    w.writeLines(1, topModule.ports flatMap emitPort(topLevel = true))





    val extModuleDecs = extModulesAndPrefixes map { case (module, fullName) => {
      // val instanceName = fullName.split("\\.").last
      val instanceName = removeDots(fullName).dropRight(1)
      s"$module $instanceName;"
    }}

    w.writeLines(1, extModuleDecs)
    w.writeLines(0, s"")

    w.writeLines(1, "// Public data structure")
    w.writeLines(1, s"${outsideCircuitDataStructTypeName} ${rn.outsideDSName};")
    dedupInfo.dedupInstanceNameList.zipWithIndex.foreach{case (name: String, idx: Int) => {
      w.writeLines(1, s"// Private data structure for dedup instance ${name}")
      w.writeLines(1, s"${dedupCircuitDataStructTypeName} ${rn.getDedupInstanceDSName(idx)};")
    }}
    w.writeLines(0, s"")
    w.writeLines(1, s"$topName() {")

    w.writeLines(2, initializeVals(topLevel = true)(topModule, topModuleRegisters, topModuleMemories))
    w.writeLines(2, s"${rn.outsideDSName}.init();")
    dedupInfo.dedupInstanceNameList.zipWithIndex.foreach{case (name: String, idx: Int) => {
      w.writeLines(2, s"${rn.getDedupInstanceDSName(idx)}.init();")
    }}

    w.writeLines(2, s"// Setup pointers for all instances")
    dedupInfo.dedupAccessedMemoryByInst(dedupInfo.dedupMainInstanceName).foreach{memName => {
      val memShortName = memName.stripPrefix(dedupInfo.dedupMainInstanceName)
      val dedupDeclName = removeDots(memShortName)
      dedupInfo.dedupInstanceNameList.zipWithIndex.foreach{case (instanceName: String, idx: Int) => {
        val globalDSName = rn.outsideDSName
        val dedupDSName = rn.getDedupInstanceDSName(idx)
        val correspondingMemName = instanceName + memShortName
        val memGlobalName = removeDots(correspondingMemName)

        w.writeLines(2, s"${dedupDSName}.${dedupDeclName} = ${globalDSName}.${memGlobalName};")
      }}
    }}

    w.writeLines(1, "}")

    w.writeLines(0, s"")
  }


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute(circuit: Circuit, annotations: AnnotationSeq) {
    val opt = initialOpt
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    w.writeLines(0, s"#ifndef $headerGuardName")
    w.writeLines(0, s"#define $headerGuardName")
    w.writeLines(0, "")
    w.writeLines(0, "#include <array>")
    w.writeLines(0, "#include <cstdint>")
    w.writeLines(0, "#include <cstdlib>")
    w.writeLines(0, "#include <uint.h>")
    w.writeLines(0, "#include <sint.h>")
    w.writeLines(0, "#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)")
    if (opt.trackParts || opt.trackSigs || opt.withVCD || opt.genRegDump) {
      w.writeLines(0, "#include <fstream>")
    }

    if(opt.withVCD) {
      w.writeLines(0, "uint64_t vcd_cycle_count = 0;")
      w.writeLines(1,s"""FILE *outfile;""")
    }
    val sg = StatementGraph(circuit, opt.removeFlatConnects)
    logger.info(sg.makeStatsString)
    val containsAsserts = sg.containsStmtOfType[Stop]()
    val extIOMap = findExternalPorts(circuit)
    val condPartWorker = MakeCondPart(sg, rn, extIOMap)
    rn.populateFromSG(sg, extIOMap)

    var dedupCPInfo: Option[DedupCPInfo] = None
    if (opt.useCondParts) {
      assert(opt.dedup)
      // Dedup + VCD not supported yet
      assert(!opt.withVCD)

      // Start timer
      val startTime = System.currentTimeMillis()

      // Parse module and instance information
      val modInstInfo = new ModuleInstanceInfo(circuit, annotations, sg)

      // Determine which mod/insts to dedup
      // Note: Currently only dedup 1 mod
      // 1. Find out num of instances of each module
      val modInstanceCount = modInstInfo.internalModInstanceTable.map{ case (modName, insts) => modName -> insts.size}
      // 2. Find out reduction of [#IR nodes] as dedup benefits
      val modDedupBenefits = modInstanceCount.map{ case(modName, nInst) => modName -> ((nInst - 1) * modInstInfo.internalModIRSize(modName))}
      // 3. Sort
      val modDedupBenefitsSorted = modDedupBenefits.toSeq.sortBy(_._2)(Ordering[Int].reverse)

      // Report benefits
      logger.info("=" * 50)
      logger.info("Module Name, Num of Instances, Dedup Benefits")
      for (i <- 0 to Seq(5, modDedupBenefitsSorted.size).min) {
        val modName = modDedupBenefitsSorted(i)._1
        val modDedupBenefit = modDedupBenefitsSorted(i)._2
        logger.info(s"${modName}, ${modInstanceCount(modName)}, ${modDedupBenefit}")
      }
      logger.info("=" * 50)

      // Choose which module to deduplicate (most benefit)
      val dedupMod = modDedupBenefitsSorted.head._1
      val dedupInstances = modInstInfo.allModInstanceTable(dedupMod)

      val dedupBenefit = modDedupBenefitsSorted.head._2
      val originalIRSize = sg.validNodes.size
      logger.info(s"Deduplicate module [${dedupMod}], ideal benefit (num IR nodes) ${dedupBenefit} (-${dedupBenefit.toFloat * 100 / originalIRSize}%)")
      logger.info(s"Original design has ${originalIRSize} IR nodes")
      logger.info(s"Dedup instances: ${dedupInstances}")


      val stopTime = System.currentTimeMillis()
      logger.info(s"Took ${stopTime - startTime} ms to find proper dedup module")



      if (dedupInstances.size <= 1) {
        println("Input circuit contains no duplicated modules!")
        condPartWorker.doOpt((opt.partCutoff))
      } else {
        logger.info("Start working on dedup optimization")
        dedupCPInfo = Some(condPartWorker.doOptForDedup(opt.partCutoff, dedupInstances, modInstInfo))
      }

    } else {
      if (opt.regUpdates)
        OptElideRegUpdates(sg)
      if (opt.conditionalMuxes)
        MakeCondMux(sg, rn, Set())
    }
    checkRegResetSafety(sg)
    if (opt.trackParts || opt.trackSigs || opt.trackExts)
      actTrac.declareTop(sg, topName, condPartWorker)

    dedupCPInfo match {
      case None => {
        // No dedup
        circuit.modules foreach {
          case m: Module => declareModule(m, topName)
          case m: ExtModule => declareExtModule(m)
        }
      }
      case Some(dedupInfo) => {
        circuit.modules foreach {
          case m: ExtModule => declareExtModule(m)
          case _ => Nil
        }
        declareFlattenModules(sg, dedupInfo)
      }
    }

    val topModule = findModule(topName, circuit) match {case m: Module => m}
    if (initialOpt.writeHarness) {
      w.writeLines(0, "")
      w.writeLines(1, s"void connect_harness(CommWrapper<struct $topName> *comm) {")
      w.writeLines(2, HarnessGenerator.harnessConnections(topModule))
      w.writeLines(1, "}")
      w.writeLines(0, "")
    }
    if (opt.withVCD)  { vcd.get.declareOldvaluesAll(circuit) }
    if(opt.withVCD) { vcd.get.genWaveHeader() }
    if (containsAsserts) {
      w.writeLines(1, "bool assert_triggered = false;")
      w.writeLines(1, "int assert_exit_code;")
      w.writeLines(0, "")
    }
    if (opt.useCondParts) {
      dedupCPInfo match {
        case None => {
          // No dedup
          writeZoningPredecs(sg, condPartWorker, circuit.main, extIOMap, opt)
        }
        case Some(dedupInfo) => {
          writeZoningPredecsForDedup(sg, condPartWorker, circuit.main, extIOMap, opt, dedupInfo)
        }
      }
    }
    w.writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
    if(opt.withVCD) { vcd.get.initializeOldValues(circuit) }
    if (opt.trackParts || opt.trackSigs)
      w.writeLines(2, "act_cycle_count++;")
    if (opt.useCondParts) {
      dedupCPInfo match {
        case None => {
          // No dedup
          writeZoningBody(sg, condPartWorker, opt)
        }
        case Some(dedupInfo) => {
          writeZoningBodyForDedup(sg, condPartWorker, opt, dedupInfo)
        }
      }
    } else
      writeBodyInner(2, sg, opt)
    if(opt.withVCD) { vcd.get.compareOldValues(circuit) }
    if (containsAsserts) {
      w.writeLines(2, "if (done_reset && update_registers && assert_triggered) {")
      w.writeLines(3, "printf(\"Assertion triggered, exit...\\n\");")
      w.writeLines(3, "exit(assert_exit_code);")
      w.writeLines(2, "}")

      w.writeLines(2, "if (!done_reset) assert_triggered = false;")
    }
    w.writeLines(0, "")
    if(opt.withVCD) { vcd.get.assignOldValues(circuit) }
    w.writeLines(2, "")
    w.writeLines(1, "}")
    // if (opt.trackParts || opt.trackSigs) {
    //   w.writeLines(1, s"~$topName() {")
    //   w.writeLines(2, "writeActToJson();")
    //   w.writeLines(1, "}")
    // }
    w.writeLines(0, "")
    w.writeLines(0, "")
    w.writeLines(0, s"} $topName;") //closing top module dec
    w.writeLines(0, "")
    w.writeLines(0, s"#endif  // $headerGuardName")
  }
}


class EssentCompiler(opt: OptFlags) {

  // VerilogMemDelays: compiling memory latencies to combinational-read memories with delay pipelines.
  // This pass eliminates mems with read latency = 1 (introduced by CHIRRTL smem)
  // and thus satisfy essent.pass.FactorMemReads (memHasRightParams)

  // ConvertAsserts: Convert Verification IR (with op == Formal.Assert) into conventional print statement

  val readyForEssent: Seq[TransformDependency] =
    Seq(
      Dependency(firrtl.passes.memlib.VerilogMemDelays),
      Dependency(essent.passes.RemoveFormalNCover),
      Dependency(firrtl.transforms.formal.ConvertAsserts)
    ) ++
    firrtl.stage.Forms.LowFormOptimized ++
    Seq(
//      Dependency(essent.passes.LegacyInvalidNodesForConds),
      Dependency(essent.passes.ReplaceAsyncRegs),
      Dependency(essent.passes.NoClockConnects),
      Dependency(essent.passes.RegFromMem1),
      Dependency(essent.passes.FactorMemReads),
      Dependency(essent.passes.FactorMemWrites),
      Dependency(essent.passes.SplitRegUpdates),
      Dependency(essent.passes.FixMulResultWidth),
      Dependency(essent.passes.DistinctTypeInstNames),
      Dependency(essent.passes.RemoveAsAsyncReset),
      Dependency(essent.passes.ReplaceRsvdKeywords)
    )

  def compileAndEmit(circuit: Circuit) {
    val topName = circuit.main
    if (opt.writeHarness) {
      val harnessFilename = new File(opt.outputDir, s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      if (opt.withVCD) { HarnessGenerator.topFile(topName, harnessWriter," |  dut.genWaveHeader();") }
      else { HarnessGenerator.topFile(topName, harnessWriter, "")}
      harnessWriter.close()
    }
    val firrtlCompiler = new transforms.Compiler(readyForEssent)
    val resultState = firrtlCompiler.execute(CircuitState(circuit, Seq()))
    if (opt.dumpLoFirrtl) {
      val debugWriter = new FileWriter(new File(opt.outputDir, s"$topName.lo.fir"))
      debugWriter.write(resultState.circuit.serialize)
      debugWriter.close()
    }


    val dutWriter = new FileWriter(new File(opt.outputDir, s"$topName.h"))
    val emitter = new EssentEmitter(opt, dutWriter,resultState.circuit)
    emitter.execute(resultState.circuit, resultState.annotations)
    dutWriter.close()
  }
}
