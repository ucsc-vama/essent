package essent

import java.io.{File, FileWriter, Writer}

import essent.Emitter._
import essent.Extract._
import essent.ir._
import essent.Util._
import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.stage.TransformManager.TransformDependency
import firrtl.stage.transforms

import logger._


class EssentEmitter(initialOpt: OptFlags, writer: Writer) extends LazyLogging {
  val tabs = "  "
  val flagVarName = "PARTflags"
  val actVarName = "ACTcounts"
  val sigTrackName = "SIGcounts"
  val sigActName = "SIGact"
  val sigExtName = "SIGext"
  var sigNameToID = Map[String,Int]()

  implicit val rn = new Renamer


  // parallel function name
  def gen_tp_eval_name(pid: Int) = s"eval_tp_$pid"
  def gen_tp_wsync_name(pid: Int) = s"sync_tp_$pid"

  def gen_thread_func_name(tid: Int) = s"worker_thread_${tid}"
  def gen_thread_obj_name(tid: Int) = s"thread_${tid}"
  def gen_thread_eval_token_name(tid: Int) = s"thread_${tid}_eval_token"
  def gen_thread_sync_token_name(tid: Int) = s"thread_${tid}_sync_token"

  // Writing To File
  //----------------------------------------------------------------------------
  def writeLines(indentLevel: Int, lines: String) {
    writeLines(indentLevel, Seq(lines))
  }

  def writeLines(indentLevel: Int, lines: Seq[String]) {
    lines foreach { s => writer write tabs*indentLevel + s + "\n" }
  }


  def declareFlattenSubModule(c: Circuit): Unit = {
    val topName = c.main
    val modules = c.modules.collect {case m: Module => m}
    val extModules = c.modules.collect {case e: ExtModule => e}

    val moduleDict = modules.map(x => (x.name, x)).toMap
    val extModuleDict = extModules.map(x => (x.name, x)).toMap

    val topModule = moduleDict(topName)
    // TODO : remove top module
    val modulesAndPrefixes = findAllModuleInstances(c) filter {case (modName, _) => moduleDict.contains(modName)}


    val registerDesc = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val registers = findInstancesOf[DefRegister](moduleDict(moduleName).body)
      registers flatMap {d: DefRegister => {
        val typeStr = genCppType(d.tpe)
        val regName = d.name
        Seq(s"$typeStr ${prefix_rename}$regName;")
      }}
    }}

    val memoryDesc = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories map {m: DefMemory => {
        s"${genCppType(m.dataType)} ${prefix_rename}${m.name}[${m.depth}];"
      }}
    }}



    val registerInit = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val registers = findInstancesOf[DefRegister](moduleDict(moduleName).body)
      registers flatMap {d: DefRegister => {
        val regName = d.name
        Seq(s"${prefix_rename}${regName}.rand_init();")
      }}
    }}

    val memoryInit = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories flatMap {m: DefMemory => {
        val mem_name = s"${prefix_rename}${m.name}"
        if ((m.depth > 1000) && (bitWidth(m.dataType)) <= 64) {
          Seq(s"${mem_name}[0].rand_init();",
            s"for (size_t a=0; a < ${m.depth}; a++) ${mem_name}[a] = ${mem_name}[0].as_single_word() + a;")
        } else {
          Seq(s"for (size_t a=0; a < ${m.depth}; a++) ${mem_name}[a].rand_init();")
        }
      }}
    }}


    val modName = "DesignData"



    writeLines(0, "")
    writeLines(0, s"typedef struct ${modName} {")
    writeLines(0, "")
    writeLines(1, "// Registers")
    writeLines(1, registerDesc)
    writeLines(0, "")
    writeLines(1, "// Memories")
    writeLines(1, memoryDesc)
    // No need emit port. This would not be the top level
    //    writeLines(1, m.ports flatMap emitPort(modName == topName))
    // No need to declare moduleDesc, as the whole design is flattened
    //    writeLines(1, moduleDecs)
    writeLines(0, "")


    // Constructor
    writeLines(1, s"$modName() {")

    writeLines(2, registerInit)
    writeLines(2, memoryInit)


    writeLines(1, "}")

    writeLines(0, s"} $modName;")

  }



  def declareFlattenSubModule(c: Circuit, part_write: Seq[Seq[Statement]]): Unit = {
    val topName = c.main
    val modules = c.modules.collect {case m: Module => m}
    val extModules = c.modules.collect {case e: ExtModule => e}

    val moduleDict = modules.map(x => (x.name, x)).toMap
    val extModuleDict = extModules.map(x => (x.name, x)).toMap

    val topModule = moduleDict(topName)
    // TODO : remove top module
    val modulesAndPrefixes = findAllModuleInstances(c) filter {case (modName, _) => moduleDict.contains(modName)}


    val allRegisters = part_write.map(_.collect {case ru: RegUpdate => ru})
    val allMemories = part_write.flatten.collect {case mw: MemWrite => mw}

    val registerDesc = allRegisters.map(_.flatMap {ru => {
      ru.regRef match {
        case reg: Reference => {
          val typeStr = genCppType(reg.tpe)
          val regName = reg.name
          val genName = regName.replace('.', '_')
          Seq(s"$typeStr ${genName};")
        }
        case _ => Seq()
      }

    }})



    val memoryDesc = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories map {m: DefMemory => {
        s"${genCppType(m.dataType)} ${prefix_rename}${m.name}[${m.depth}];"
      }}
    }}



    val registerInit = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val registers = findInstancesOf[DefRegister](moduleDict(moduleName).body)
      registers flatMap {d: DefRegister => {
        val regName = d.name
        Seq(s"${prefix_rename}${regName}.rand_init();")
      }}
    }}

    val memoryInit = modulesAndPrefixes.flatMap{case (moduleName, prefix) => {
      val prefix_rename = prefix.replace('.', '_')
      val memories = findInstancesOf[DefMemory](moduleDict(moduleName).body)
      memories flatMap {m: DefMemory => {
        val mem_name = s"${prefix_rename}${m.name}"
        if ((m.depth > 1000) && (bitWidth(m.dataType)) <= 64) {
          Seq(s"${mem_name}[0].rand_init();",
            s"for (size_t a=0; a < ${m.depth}; a++) ${mem_name}[a] = ${mem_name}[0].as_single_word() + a;")
        } else {
          Seq(s"for (size_t a=0; a < ${m.depth}; a++) ${mem_name}[a].rand_init();")
        }
      }}
    }}


    val modName = "DesignData"


    writeLines(0, "")
    writeLines(0, s"typedef struct ${modName} {")
    writeLines(0, "")
    writeLines(1, "// Registers")

    registerDesc.zipWithIndex.foreach{case(p, i) => {
      writeLines(0, "")
      writeLines(1, s"// Registers for partition ${i}")
      writeLines(1, p)

    }}

    writeLines(0, "")
    writeLines(1, "// Memories")
    writeLines(1, memoryDesc)
    // No need emit port. This would not be the top level
    //    writeLines(1, m.ports flatMap emitPort(modName == topName))
    // No need to declare moduleDesc, as the whole design is flattened
    //    writeLines(1, moduleDecs)
    writeLines(0, "")


    // Constructor
    writeLines(1, s"$modName() {")

    writeLines(2, registerInit)
    writeLines(2, memoryInit)


    writeLines(1, "}")

    writeLines(0, s"} $modName;")

  }



  // Declaring Top level Module. This function is used only by parallel version
  //----------------------------------------------------------------------------
  def declareTopModule(m: Module, c: Circuit) {
    val topName = m.name

    val extModules = c.modules.collect {case e: ExtModule => e}
    val extModuleDict = extModules.map(x => (x.name, x)).toMap

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
    val extModulesAndPrefixes = modulesAndPrefixes.filter{case(modName, _) => {extModuleDict.contains(modName)}}
    val extModuleDecs = extModulesAndPrefixes map { case (module, fullName) => {
      val instanceName = fullName.split("\\.").last
      s"$module $instanceName;"
    }}
    val modName = m.name
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, registerDecs)
    writeLines(1, memDecs)
    writeLines(1, m.ports flatMap emitPort(modName == topName))
    writeLines(1, extModuleDecs)
    writeLines(1, s"DesignData ${getGlobalDataName()};")
    writeLines(0, "")

    val worker_thread_count = initialOpt.parallel - 1

    for (tid <- 1 to worker_thread_count) {
      writeLines(1, s"std::atomic<bool> ${gen_thread_eval_token_name(tid)};")
      writeLines(1, s"std::atomic<bool> ${gen_thread_sync_token_name(tid)};")
    }
    writeLines(0, "")
    writeLines(1, s"bool sim_token;")

    writeLines(0, "")
    for (tid <- 1 to worker_thread_count) {
      writeLines(1, s"std::thread *${gen_thread_obj_name(tid)};")
    }

    writeLines(0, "")
    writeLines(1, "bool update_registers;")
    writeLines(1, "bool verbose;")
    writeLines(1, "bool done_reset;")

    writeLines(0, "")

    // Constructor
    writeLines(1, s"$modName() {")
    writeLines(2, initializeVals(modName == topName)(m, registers, memories))


    // reset tokens
    writeLines(0, "")
    for (tid <- 1 to worker_thread_count) {
      writeLines(2, s"${gen_thread_eval_token_name(tid)}.store(false);")
      writeLines(2, s"${gen_thread_sync_token_name(tid)}.store(false);")
    }
    writeLines(0, "")
    writeLines(2, s"sim_token = true;")

    // Create worker threads
    writeLines(0, "")
    for (tid <- 1 to worker_thread_count) {
      writeLines(2, s"${gen_thread_obj_name(tid)} = new std::thread([=]() -> void { this->${gen_thread_func_name(tid)}(); });")
    }


    writeLines(1, "}")

    // Destructor
    writeLines(0, "")
    writeLines(1, s"~$modName() {")
    writeLines(2, s"sim_token = false;")
    // Join worker threads
    writeLines(0, "")
    for (tid <- 1 to worker_thread_count) {
      writeLines(2, s"${gen_thread_obj_name(tid)} -> join();")
    }
    writeLines(1, "}")

    // Thread entry point

    for (tid <- 1 to worker_thread_count) {

      writeLines(0, "")
      writeLines(1, s"void ${gen_thread_func_name(tid)}() {")
      writeLines(2, "while (true) {")
      writeLines(3, s"while (${gen_thread_eval_token_name(tid)}.load() == false && sim_token == true) {")
      writeLines(4, s"_mm_pause();")
      writeLines(3, "}")
      writeLines(3, s"if (sim_token == false) return;")

      // call task
      writeLines(3, s"${gen_tp_eval_name(tid)}(update_registers, verbose, done_reset);")

      writeLines(3, s"${gen_thread_eval_token_name(tid)}.store(false);")

      writeLines(3, s"while (${gen_thread_sync_token_name(tid)}.load() == false) {")
      writeLines(4, s"_mm_pause();")
      writeLines(3, "}")

      writeLines(3, s"${gen_tp_wsync_name(tid)}(update_registers);")


      writeLines(3, s"${gen_thread_sync_token_name(tid)}.store(false);")

      writeLines(2, "}")
      writeLines(1, "}")
    }

    // Not done yet
    writeLines(0, "")
    // writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
  }
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
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, registerDecs)
    writeLines(1, memDecs)
    writeLines(1, m.ports flatMap emitPort(modName == topName))
    writeLines(1, moduleDecs)
    writeLines(0, "")

    // Constructor
    writeLines(1, s"$modName() {")
    writeLines(2, initializeVals(modName == topName)(m, registers, memories))
    writeLines(1, "}")

    if (modName == topName) {
      writeLines(0, "")
      // writeLines(1, s"void connect_harness(CommWrapper<struct $modName> *comm);")
    } else {
      writeLines(0, s"} $modName;")
    }
  }

  def declareExtModule(m: ExtModule) {
    val modName = m.name
    writeLines(0, "")
    writeLines(0, s"typedef struct $modName {")
    writeLines(1, m.ports flatMap emitPort(true))
    writeLines(0, s"} $modName;")
  }

  def getGlobalDataName() = s"dat"
  def getThreadDataName_Reg(pid: Int) = s"tdr_$pid"
  def getThreadDataName_Mem(pid: Int) = s"tdm_$pid"
  def memNameToDeclName(mem: String) = mem.replace('.', '_')

  def declareThreadMemWriteData(writes: Seq[Statement], pid: Int, rn: Renamer) {

    val decls = writes flatMap {stmt => stmt match {
      // Don't need extra space for regwrite anymore
//      case ru: RegUpdate => {
//        val typeStr = genCppType (ru.regRef.tpe)
//        val lhs_orig = emitExpr(ru.expr)(rn)
//        Seq (s"$typeStr $lhs_orig;")
//      }
      case m: MemWrite => {

        val typeStr = genCppType(m.wrData.tpe)
        val declName = memNameToDeclName(m.nodeName())
        Seq(s"bool ${declName}_write_en;",
          s"int ${declName}_index;",
          s"$typeStr ${declName}_data;")
      }

      case _ => Seq()
    }}

    writeLines(1, s"typedef struct ThreadData_Mem_$pid {")
    writeLines(2, decls)
    writeLines(1, s"} ThreadData_$pid;")

  }



  // Write General-purpose Eval
  //----------------------------------------------------------------------------
  // TODO: move specialized CondMux emitter elsewhere?
  def writeBodyInner(indentLevel: Int, sg: StatementGraph, opt: OptFlags,
                     keepAvail: Set[String] = Set()) {
    // ng.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(stmt)) }
    if (opt.conditionalMuxes)
      MakeCondMux(sg, rn, keepAvail)
    val noMoreMuxOpts = opt.copy(conditionalMuxes = false)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), noMoreMuxOpts)
        writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), noMoreMuxOpts)
        writeLines(indentLevel, "}")
      }
      case _ => {
        writeLines(indentLevel, emitStmt(stmt))
        if (opt.trackSigs) emitSigTracker(stmt, indentLevel, opt)
      }
    }}
  }



  def writeSyncBody(indentLevel: Int, writes: Seq[Statement], pid: Int, rn: Renamer) = {
    val allRegisters = writes.collect{case ru:RegUpdate => ru}

    val registerNames = allRegisters.flatMap {ru => {
      ru.regRef match {
        case reg: Reference => {
          val regName = reg.name
          val genName = regName.replace('.', '_')
          Seq(s"${genName}")
        }
        case _ => Seq()
      }
    }}

    if (registerNames.nonEmpty) {
      // memcpy only if writes to registers
      val memcpy_src = s"reinterpret_cast<char*>(&${getThreadDataName_Reg(pid)}) + offsetof(DesignData, ${registerNames.head})"
      val memcpy_dst = s"reinterpret_cast<char*>(&${getGlobalDataName()}) + offsetof(DesignData, ${registerNames.head})"
      val memcpy_size = s"offsetof(DesignData, ${registerNames.last}) + sizeof(${getGlobalDataName()}.${registerNames.last}) - offsetof(DesignData, ${registerNames.head})"

      writeLines(indentLevel, s"std::memcpy(${memcpy_dst}, ${memcpy_src}, ${memcpy_size});")
    }


    val lines = writes flatMap  {stmt => stmt match {
      case mw: MemWrite => {
        // Seq(s"if (UNLIKELY(update_registers && ${emitExprWrap(mw.wrEn)(rn)} && ${emitExprWrap(mw.wrMask)(rn)})) ${mw.memName}[${emitExprWrap(mw.wrAddr)(rn)}.as_single_word()] = ${emitExpr(mw.wrData)(rn)};")
        val declName = memNameToDeclName(mw.nodeName())
        val var_wen = s"${getThreadDataName_Mem(pid)}.${declName}_write_en"
        val var_index = s"${getThreadDataName_Mem(pid)}.${declName}_index"
        val var_data = s"${getThreadDataName_Mem(pid)}.${declName}_data"

        val memName = s"${getGlobalDataName()}.${mw.memName.replace('.', '_')}"

        Seq(s"if (UNLIKELY(update_registers && ${var_wen})) ${memName}[${var_index}] = ${var_data};")
      }

//      case ru: RegUpdate => {
//        val lhs_orig = emitExpr(ru.expr)(rn)
//        Seq(s"if (update_registers) ${emitExpr(ru.regRef)} = ${getThreadDataName_Reg(pid)}.${lhs_orig};")
//      }
      case _ => Seq()
    }}

    writeLines(indentLevel, lines)
  }


  def writeBodyInner_TP(indentLevel: Int, sg: StatementGraph, opt: OptFlags, pid: Int,
                     keepAvail: Set[String] = Set()) {
    // ng.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(stmt)) }
    if (opt.conditionalMuxes)
      MakeCondMux(sg, rn, keepAvail)
    val noMoreMuxOpts = opt.copy(conditionalMuxes = false)

    def changePrefix(st: String, from: String, to: String) = st.replace(from, to)

//    def stmtNeedDeferred(stmt: Statement) = {stmt match {
//      case m: MemWrite => true
//      case ru: RegUpdate => true
//      case _ => false
//    }}

    val stmtsOrdered = sg.stmtsOrdered()
//    val stmtsOrdered_deferRegMem = stmtsOrdered.filterNot(stmtNeedDeferred) ++
//      Seq(CodeGen("#pragma omp barrier")) ++
//      stmtsOrdered.filter(stmtNeedDeferred)

    stmtsOrdered foreach { stmt => stmt match {
      case cm: CondMux => {
        if (rn.nameToMeta(cm.name).decType == MuxOut)
          writeLines(indentLevel, s"${genCppType(cm.mux.tpe)} ${rn.emit(cm.name)};")
        val muxCondRaw = emitExpr(cm.mux.cond)
        val muxCond = if (muxCondRaw == "reset") s"UNLIKELY($muxCondRaw)" else muxCondRaw
        writeLines(indentLevel, s"if (UNLIKELY($muxCond)) {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.tWay), noMoreMuxOpts)
        writeLines(indentLevel, "} else {")
        writeBodyInner(indentLevel + 1, StatementGraph(cm.fWay), noMoreMuxOpts)
        writeLines(indentLevel, "}")
      }
      case _ => {
        def emitStmt_T(s: Statement)(rn: Renamer) = s match {
          case mw: MemWrite => {
            // Seq(s"if (UNLIKELY(update_registers && ${emitExprWrap(mw.wrEn)(rn)} && ${emitExprWrap(mw.wrMask)(rn)})) ${mw.memName}[${emitExprWrap(mw.wrAddr)(rn)}.as_single_word()] = ${emitExpr(mw.wrData)(rn)};")
            val declName = memNameToDeclName(mw.nodeName())
            Seq(s"${getThreadDataName_Mem(pid)}.${declName}_write_en = ${emitExprWrap(mw.wrEn)(rn)} && ${emitExprWrap(mw.wrMask)(rn)};",
              s"${getThreadDataName_Mem(pid)}.${declName}_index = ${emitExprWrap(mw.wrAddr)(rn)}.as_single_word();",
              s"${getThreadDataName_Mem(pid)}.${declName}_data = ${emitExpr(mw.wrData)(rn)};")
          }

//          case ru: RegUpdate => {
//            val lhs_orig = emitExpr(ru.expr)(rn)
//            Seq(s"${getThreadDataName_Reg(pid)}.${lhs_orig} = ${emitExpr(ru.expr)(rn)};")
//          }
          case ru: RegUpdate => Seq(s"if (update_registers /**/) ${changePrefix(emitExpr(ru.regRef)(rn), "dat.", getThreadDataName_Reg(pid) + ".")} = ${emitExpr(ru.expr)(rn)};")

          case _ => emitStmt(s)(rn)
        }
        writeLines(indentLevel, emitStmt_T(stmt)(rn))
        if (opt.trackSigs) emitSigTracker(stmt, indentLevel, opt)
      }
    }}
  }


  def writeRegResetOverrides(sg: StatementGraph) {
    val updatesWithResets = sg.allRegDefs filter { r => emitExpr(r.reset) != "UInt<1>(0x0)" }
    assert(updatesWithResets.isEmpty)
//    val resetGroups = updatesWithResets.groupBy(r => emitExpr(r.reset))
//    val overridesToWrite = resetGroups.toSeq flatMap {
//      case (resetName, regDefs) => {
//        val body = regDefs map {
//          r => s"$tabs${rn.emit(r.name)} = ${emitExpr(r.init)};"
//        }
//        Seq(s"if ($resetName) {") ++ body ++ Seq("}")
//      }
//    }
//    if (overridesToWrite.nonEmpty) {
//      writeLines(2, "if (update_registers) {")
//      // FUTURE: will overrides need triggers if partitioned?
//      writeLines(3, overridesToWrite)
//      writeLines(2, "}")
//    }
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

  def writeZoningPredecs(
                          sg: StatementGraph,
                          condPartWorker: MakeCondPart,
                          topName: String,
                          extIOtypes: Map[String, Type],
                          opt: OptFlags) {
    // predeclare part outputs
    val outputPairs = condPartWorker.getPartOutputsToDeclare()
    val outputConsumers = condPartWorker.getPartInputMap()
    writeLines(1, outputPairs map {case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name)};"})
    val extIOCacheDecs = condPartWorker.getExternalPartInputTypes(extIOtypes) map {
      case (name, tpe) => s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)};"
    }
    writeLines(1, extIOCacheDecs)
    writeLines(1, s"std::array<bool,${condPartWorker.getNumParts()}> $flagVarName;")
    // FUTURE: worry about namespace collisions with user variables
    writeLines(1, s"bool sim_cached = false;")
    writeLines(1, s"bool regs_set = false;")
    writeLines(1, s"bool update_registers;")
    writeLines(1, s"bool done_reset;")
    writeLines(1, s"bool verbose;")
    writeLines(0, "")
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        writeLines(1, s"void ${genEvalFuncName(cp.id)}() {")
        if (!cp.alwaysActive)
          writeLines(2, s"$flagVarName[${cp.id}] = false;")
        if (opt.trackParts)
          writeLines(2, s"$actVarName[${cp.id}]++;")

        val cacheOldOutputs = cp.outputsToDeclare.toSeq map {
          case (name, tpe) => { s"${genCppType(tpe)} ${rn.emit(name + condPartWorker.cacheSuffix)} = ${rn.emit(name)};"
        }}
        writeLines(2, cacheOldOutputs)
        val (regUpdates, noRegUpdates) = partitionByType[RegUpdate](cp.memberStmts)
        val keepAvail = (cp.outputsToDeclare map { _._1 }).toSet
        writeBodyInner(2, StatementGraph(noRegUpdates), opt, keepAvail)
        writeLines(2, genAllTriggers(cp.outputsToDeclare.keys.toSeq, outputConsumers, condPartWorker.cacheSuffix))
        val regUpdateNamesInPart = regUpdates flatMap findResultName
        writeLines(2, genAllTriggers(regUpdateNamesInPart, outputConsumers, "$next"))
        // triggers for MemWrites
        val memWritesInPart = cp.memberStmts collect { case mw: MemWrite => mw }
        val memWriteTriggers = memWritesInPart flatMap { mw => {
          val condition = s"${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)}"
          genDepPartTriggers(outputConsumers.getOrElse(mw.memName, Seq()), condition)
        }}
        writeLines(2, memWriteTriggers)
        writeLines(2, regUpdates flatMap emitStmt)
        writeLines(1, "}")
      }
      case _ => throw new Exception(s"Statement at top-level is not a CondPart (${stmt.serialize})")
    }}
    writeLines(0, "")
  }

  def writeZoningBody(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags) {
    writeLines(2, "if (reset || !done_reset) {")
    writeLines(3, "sim_cached = false;")
    writeLines(3, "regs_set = false;")
    writeLines(2, "}")
    writeLines(2, "if (!sim_cached) {")
    writeLines(3, s"$flagVarName.fill(true);")
    writeLines(2, "}")
    writeLines(2, "sim_cached = regs_set;")
    writeLines(2, "this->update_registers = update_registers;")
    writeLines(2, "this->done_reset = done_reset;")
    writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    writeLines(2, extIOCaches.toSeq)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        if (!cp.alwaysActive)
          writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
        else
          writeLines(2, s"${genEvalFuncName(cp.id)}();")
      }
      case _ => writeLines(2, emitStmt(stmt))
    }}
    // writeLines(2,  "#ifdef ALL_ON")
    // writeLines(2, s"$flagVarName.fill(true);" )
    // writeLines(2,  "#endif")
    writeLines(2, "regs_set = true;")
  }


  def writeZoningBody_TP(sg: StatementGraph, condPartWorker: MakeCondPart, opt: OptFlags, pid: Int) {
    writeLines(2, "if (reset || !done_reset) {")
    writeLines(3, "sim_cached = false;")
    writeLines(3, "regs_set = false;")
    writeLines(2, "}")
    writeLines(2, "if (!sim_cached) {")
    writeLines(3, s"$flagVarName.fill(true);")
    writeLines(2, "}")
    writeLines(2, "sim_cached = regs_set;")
    writeLines(2, "this->update_registers = update_registers;")
    writeLines(2, "this->done_reset = done_reset;")
    writeLines(2, "this->verbose = verbose;")
    val outputConsumers = condPartWorker.getPartInputMap()
    val externalPartInputNames = condPartWorker.getExternalPartInputNames()
    // do activity detection on other inputs (external IOs and resets)
    writeLines(2, genAllTriggers(externalPartInputNames, outputConsumers, condPartWorker.cacheSuffix))
    // cache old versions
    val extIOCaches = externalPartInputNames map {
      sigName => s"${rn.emit(sigName + condPartWorker.cacheSuffix)} = ${rn.emit(sigName)};"
    }
    writeLines(2, extIOCaches.toSeq)
    sg.stmtsOrdered foreach { stmt => stmt match {
      case cp: CondPart => {
        if (!cp.alwaysActive)
          writeLines(2, s"if (UNLIKELY($flagVarName[${cp.id}])) ${genEvalFuncName(cp.id)}();")
        else
          writeLines(2, s"${genEvalFuncName(cp.id)}();")
      }
      case _ => writeLines(2, emitStmt(stmt))
    }}
    // writeLines(2,  "#ifdef ALL_ON")
    // writeLines(2, s"$flagVarName.fill(true);" )
    // writeLines(2,  "#endif")
    writeLines(2, "regs_set = true;")
  }


  def declareSigTracking(sg: StatementGraph, topName: String, opt: OptFlags) {
    val allNamesAndTypes = sg.collectValidStmts(sg.nodeRange) flatMap findStmtNameAndType
    sigNameToID = (allNamesAndTypes map { _._1 }).zipWithIndex.toMap
    writeLines(0, "")
    writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigTrackName{};")
    if (opt.trackExts) {
      writeLines(0, s"std::array<bool,${sigNameToID.size}> $sigActName{};")
      writeLines(0, s"std::array<uint64_t,${sigNameToID.size}> $sigExtName{};")
    }
    writeLines(0, "namespace old {")
    writeLines(1, allNamesAndTypes map {
      case (name, tpe) => s"${genCppType(tpe)} ${name.replace('.','$')};"
    })
    writeLines(0, "}")
  }

  def emitSigTracker(stmt: Statement, indentLevel: Int, opt: OptFlags) {
    stmt match {
      case mw: MemWrite =>
      case _ => {
        val resultName = findResultName(stmt)
        resultName match {
          case Some(name) => {
            val cleanName = name.replace('.','$')
            writeLines(indentLevel, s"$sigTrackName[${sigNameToID(name)}] += $name != old::$cleanName ? 1 : 0;")
            if (opt.trackExts) {
              writeLines(indentLevel, s"$sigActName[${sigNameToID(name)}] = $name != old::$cleanName;")
              val depNames = findDependencesStmt(stmt).head.deps
              val trackedDepNames = depNames filter sigNameToID.contains
              val depTrackers = trackedDepNames map {name => s"$sigActName[${sigNameToID(name)}]"}
              val anyDepActive = depTrackers.mkString(" || ")
              if (anyDepActive.nonEmpty)
                writeLines(indentLevel, s"$sigExtName[${sigNameToID(name)}] += !$sigActName[${sigNameToID(name)}] && ($anyDepActive) ? 1 : 0;")
            }
            writeLines(indentLevel, s"old::$cleanName = $name;")
          }
          case None =>
        }
      }
    }
  }

  def emitJsonWriter(opt: OptFlags, numParts: Int) {
    writeLines(0, "void writeActToJson() {")
    writeLines(1, "std::fstream file(\"activities.json\", std::ios::out | std::ios::binary);")
    writeLines(1, "JSON all_data;")
    if (opt.trackSigs) {
      writeLines(1, "JSON sig_acts;")
      writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      writeLines(2, s"""sig_acts[i] = JSON({"id", i, "acts", $sigTrackName[i]});""")
      writeLines(1, "}")
      writeLines(1, "all_data[\"signal-activities\"] = sig_acts;")
    }
    if (opt.trackParts) {
      writeLines(1, "JSON part_acts;")
      writeLines(1, s"for (int i=0; i<$numParts; i++) {")
      writeLines(2, s"""part_acts[i] = JSON({"id", i, "acts", $actVarName[i]});""")
      writeLines(1, "}")
      writeLines(1, "all_data[\"part-activities\"] = part_acts;")
    }
    if (opt.trackExts) {
      writeLines(1, "JSON sig_exts;")
      writeLines(1, s"for (int i=0; i<${sigNameToID.size}; i++) {")
      writeLines(2, s"""sig_exts[i] = JSON({"id", i, "exts", $sigExtName[i]});""")
      writeLines(1, "}")
      writeLines(1, "all_data[\"sig-extinguishes\"] = sig_exts;")
    }
    writeLines(1, "all_data[\"cycles\"] = cycle_count;")
    writeLines(1, "file << all_data << std::endl;")
    writeLines(1, "file.close();")
    writeLines(0, "}")
  }


  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute(circuit: Circuit) {
    val opt = initialOpt
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    writeLines(0, s"#ifndef $headerGuardName")
    writeLines(0, s"#define $headerGuardName")
    writeLines(0, "")
    writeLines(0, "#include <immintrin.h>")
    writeLines(0, "#include <array>")
    writeLines(0, "#include <thread>")
    writeLines(0, "#include <atomic>")
    writeLines(0, "#include <cstdint>")
    writeLines(0, "#include <cstdlib>")
    writeLines(0, "#include <uint.h>")
    writeLines(0, "#include <sint.h>")
    writeLines(0, "#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)")
    if (opt.trackParts || opt.trackSigs) {
      writeLines(0, "#include <fstream>")
      writeLines(0, "#include \"../SimpleJSON/json.hpp\"")
      writeLines(0, "using json::JSON;")
      writeLines(0, "uint64_t cycle_count = 0;")
    }
//    writeLines(0, "uint64_t debug_cycle_count = 0;")
    val sg = StatementGraph(circuit, opt.removeFlatConnects)
    logger.info(sg.makeStatsString)


    val containsAsserts = sg.containsStmtOfType[Stop]()
    val extIOMap = findExternalPorts(circuit)

    rn.populateFromSG(sg, extIOMap)

    // if (opt.trackSigs)
    //   declareSigTracking(sg, topName, opt)
    // if (opt.trackParts)
    //   writeLines(1, s"std::array<uint64_t,${sg.getNumParts()}> $actVarName{};")
    // if (opt.trackParts || opt.trackSigs)
    //    emitJsonWriter(opt, condPartWorker.getNumParts())
    // if (opt.partStats)
    //   sg.dumpPartInfoToJson(opt, sigNameToID)
    // if (opt.trackExts)
    //   sg.dumpNodeTypeToJson(sigNameToID)
    // sg.reachableAfter(sigNameToID)


    if (opt.parallel > 1) {


      val pg = PartGraph(sg)

      val tp = ThreadPartitioner(pg, opt)
      tp.doOpt()

      val part_write_stmts = tp.parts_write.map(_.map(sg.idToStmt(_)).toSeq).toSeq



      declareFlattenSubModule(circuit, part_write_stmts)

      circuit.modules foreach {
        case m: ExtModule => declareExtModule(m)
        case _ => Unit
      }

      val topModule = findModule(topName, circuit) match {case m: Module => m}
      declareTopModule(topModule, circuit)

      if (initialOpt.writeHarness) {
        writeLines(0, "")
        writeLines(1, s"void connect_harness(CommWrapper<struct $topName> *comm) {")
        writeLines(2, HarnessGenerator.harnessConnections(topModule))
        writeLines(1, "}")
        writeLines(0, "")
      }
      if (containsAsserts) {
        writeLines(1, "bool assert_triggered = false;")
        writeLines(1, "int assert_exit_code;")
        writeLines(0, "")
      }





      val worker_thread_count = initialOpt.parallel - 1

      // data structure for each part
      tp.parts.indices.foreach {pid => {
        val part_write_stmts = tp.parts_write(pid) map sg.idToStmt
        declareThreadMemWriteData(part_write_stmts.toSeq, pid, rn)
        writeLines(1, s"ThreadData_Mem_$pid ${getThreadDataName_Mem(pid)};")

        writeLines(1, s"DesignData ${getThreadDataName_Reg(pid)};")
      }}

      // For each part
      tp.parts.zipWithIndex.foreach {case(part, pid) => {
        // Modify valid nodes
        sg.validNodes --= sg.validNodes
        sg.validNodes ++= part


        val condPartWorker = MakeCondPart(sg, rn, extIOMap)

        if (opt.useCondParts) {
          throw new Exception("Parallel for O3 not supported yet")
          condPartWorker.doOpt(opt.partCutoff)
        } else {
          if (opt.regUpdates)
            OptElideRegUpdates(sg)
        }

//        if (containsAsserts) {
//          writeLines(1, s"bool assert_triggered_$pid = false;")
//          writeLines(1, s"int assert_exit_code_$pid;")
//          writeLines(0, "")
//        }

        if (opt.useCondParts)
          writeZoningPredecs(sg, condPartWorker, circuit.main, extIOMap, opt)
        writeLines(1, s"void ${gen_tp_eval_name(pid)}(bool update_registers, bool verbose, bool done_reset) {")
        if ((opt.trackParts || opt.trackSigs))
          writeLines(2, "cycle_count++;")
        if (opt.useCondParts)
          writeZoningBody_TP(sg, condPartWorker, opt, pid)
        else
          writeBodyInner_TP(2, sg, opt, pid)
        if (containsAsserts) {
          writeLines(2, s"if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
          writeLines(2, s"if (!done_reset) assert_triggered = false;")
        }

        writeRegResetOverrides(sg)
        writeLines(1, "}")
        // if (opt.trackParts || opt.trackSigs) {
        //   writeLines(1, s"~$topName() {")
        //   writeLines(2, "writeActToJson();")
        //   writeLines(1, "}")
        // }

        writeLines(1, "")

        // Function for sync registers to global copy
        writeLines(1, s"void ${gen_tp_wsync_name(pid)}(bool update_registers) {")
        val part_write_stmts = tp.parts_write(pid) map sg.idToStmt

        writeSyncBody(2, part_write_stmts.toSeq, pid, rn)
        writeLines(1, s"}")

      }}

      writeLines(0, "")


      writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
      if ((opt.trackParts || opt.trackSigs)) {
        writeLines(2, "cycle_count++;")
      }

      writeLines(2, "this->update_registers = update_registers;")
      writeLines(2, "this->verbose = verbose;")
      writeLines(2, "this->done_reset = done_reset;")

      writeLines(0, "")
      for (tid <- 1 to worker_thread_count) {
        writeLines(2, s"${gen_thread_eval_token_name(tid)}.store(true);")
      }

      writeLines(0, "")
      // Main thread is also an worker thread
      writeLines(2, s"${gen_tp_eval_name(0)}(update_registers, verbose, done_reset);")

      writeLines(0, "")

      // Wait eval complete
      for (tid <- 1 to worker_thread_count) {
        writeLines(2, s"while (${gen_thread_eval_token_name(tid)}.load() == true) {")
        writeLines(3, s"_mm_pause();")
        writeLines(2, s"};")
      }

      writeLines(0, "")

      for (tid <- 1 to worker_thread_count) {
        writeLines(2, s"${gen_thread_sync_token_name(tid)}.store(true);")
      }

      writeLines(0, "")
      writeLines(2, s"${gen_tp_wsync_name(0)}(update_registers);")

      // Wait sync complete
      for (tid <- 1 to worker_thread_count) {
        writeLines(2, s"while (${gen_thread_sync_token_name(tid)}.load() == true) {")
        writeLines(3, s"_mm_pause();")
        writeLines(2, s"};")
      }



//      writeLines(2, "debug_cycle_count ++;")
//      writeLines(2, "if (debug_cycle_count % 10000 == 0) std::cout << debug_cycle_count << std::endl;")
      writeLines(1, "}")
    } else {
      // non parallel

      circuit.modules foreach {
        case m: Module => declareModule(m, topName)
        case m: ExtModule => declareExtModule(m)
      }
      val topModule = findModule(topName, circuit) match {case m: Module => m}
      if (initialOpt.writeHarness) {
        writeLines(0, "")
        writeLines(1, s"void connect_harness(CommWrapper<struct $topName> *comm) {")
        writeLines(2, HarnessGenerator.harnessConnections(topModule))
        writeLines(1, "}")
        writeLines(0, "")
      }
      if (containsAsserts) {
        writeLines(1, "bool assert_triggered = false;")
        writeLines(1, "int assert_exit_code;")
        writeLines(0, "")
      }

      val condPartWorker = MakeCondPart(sg, rn, extIOMap)

      if (opt.useCondParts) {
        condPartWorker.doOpt(opt.partCutoff)
      } else {
        if (opt.regUpdates)
          OptElideRegUpdates(sg)
      }
      // if (opt.trackSigs)
      //   declareSigTracking(sg, topName, opt)
      // if (opt.trackParts)
      //   writeLines(1, s"std::array<uint64_t,${sg.getNumParts()}> $actVarName{};")
      // if (opt.trackParts || opt.trackSigs)
      //    emitJsonWriter(opt, condPartWorker.getNumParts())
      // if (opt.partStats)
      //   sg.dumpPartInfoToJson(opt, sigNameToID)
      // if (opt.trackExts)
      //   sg.dumpNodeTypeToJson(sigNameToID)
      // sg.reachableAfter(sigNameToID)

      if (opt.useCondParts)
        writeZoningPredecs(sg, condPartWorker, circuit.main, extIOMap, opt)
      writeLines(1, s"void eval(bool update_registers, bool verbose, bool done_reset) {")
      if (opt.trackParts || opt.trackSigs)
        writeLines(2, "cycle_count++;")
      if (opt.useCondParts)
        writeZoningBody(sg, condPartWorker, opt)
      else
        writeBodyInner(2, sg, opt)
      if (containsAsserts) {
        writeLines(2, "if (done_reset && update_registers && assert_triggered) exit(assert_exit_code);")
        writeLines(2, "if (!done_reset) assert_triggered = false;")
      }

      writeRegResetOverrides(sg)

//      writeLines(2, "debug_cycle_count ++;")
//      writeLines(2, "if (debug_cycle_count % 10000 == 0) std::cout << debug_cycle_count << std::endl;")

      writeLines(1, "}")
      // if (opt.trackParts || opt.trackSigs) {
      //   writeLines(1, s"~$topName() {")
      //   writeLines(2, "writeActToJson();")
      //   writeLines(1, "}")
      // }
    }

    writeLines(0, s"} $topName;") //closing top module dec
    writeLines(0, "")
    writeLines(0, s"#endif  // $headerGuardName")
  }
}


class EssentCompiler(opt: OptFlags) {
  val readyForEssent: Seq[TransformDependency] =
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
      Dependency(essent.passes.ReplaceRsvdKeywords),
      Dependency(essent.passes.CheckStatistics)
    )

  def compileAndEmit(circuit: Circuit) {
    val topName = circuit.main
    if (opt.writeHarness) {
      val harnessFilename = new File(opt.outputDir, s"$topName-harness.cc")
      val harnessWriter = new FileWriter(harnessFilename)
      HarnessGenerator.topFile(topName, harnessWriter)
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
    val emitter = new EssentEmitter(opt, dutWriter)
    emitter.execute(resultState.circuit)
    dutWriter.close()
  }
}
