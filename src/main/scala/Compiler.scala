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
import _root_.logger._

import scala.collection.mutable

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



  def declareFlattenSubModule(c: Circuit, part_read: Seq[Seq[Statement]], part_write: Seq[Seq[Statement]]): Unit = {
    val topName = c.main
    val modules = c.modules.collect {case m: Module => m}
    val extModules = c.modules.collect {case e: ExtModule => e}

    val moduleDict = modules.map(x => (x.name, x)).toMap
    val extModuleDict = extModules.map(x => (x.name, x)).toMap

    val topModule = moduleDict(topName)
    // TODO : remove top module
    val modulesAndPrefixes = findAllModuleInstances(c) filter {case (modName, _) => moduleDict.contains(modName)}


//    val allMemories = part_write.flatten.collect {case mw: MemWrite => mw}

    val allWriteRegisters = part_write.map(_.collect { case ru: RegUpdate => ru})
    val allReadRegisters = part_read.map(_.collect { case dr: DefRegister => dr})

    val allReadRegisterName = allReadRegisters.map(_.map(_.name))
    val allWriteRegisterName = allWriteRegisters.map(_.flatMap(_.regRef match {
      case reg: Reference => Seq(reg.name)
      case _ => Seq()
    }))

    val regNameToReadPartId = mutable.HashMap[String, Set[Int]]()
    val regNameToWritePartId = mutable.HashMap[String, Int]()

    allReadRegisterName.zipWithIndex.foreach{case (readPart, partId) => {
      readPart.foreach{reg => {
        if (!regNameToReadPartId.contains(reg)) {
          regNameToReadPartId(reg) = Set[Int]()
        }
        regNameToReadPartId(reg) += partId
      }}
    }}

    allWriteRegisterName.zipWithIndex.foreach{case (writePart, partId) => {
      writePart.foreach{reg => {
        if (regNameToWritePartId.contains(reg)) {
          throw new Exception(s"Register ${reg} is written by multiple partition")
        }
        regNameToWritePartId(reg) = partId
      }}
    }}

    val registerDesc = allWriteRegisters.zipWithIndex.map {case (partWrites, partId) => {
      val reordered = partWrites.groupBy{writeReg => {
        writeReg.regRef match {
          case regRef: Reference => {
            // It's possible that no body reading this register
            if (regNameToReadPartId.contains(regRef.name)) {
              regNameToReadPartId(regRef.name).head
            } else partId
          }
          case _ => throw new Exception("Unknown register write")
        }
      }}

      reordered.map{case (readerId, regWrites) => {
        regWrites.flatMap{_ match {
          case ru: RegUpdate => ru.regRef match {
            case reg: Reference => {
              val typeStr = genCppType(reg.tpe)
              val regName = reg.name
              val genName = regName.replace('.', '_')
//              Seq(s"$typeStr ${genName};")
              Seq((typeStr, genName))
            }
            case _ => Seq()
          }}}
      }}.toSeq
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

    registerDesc.zipWithIndex.foreach{case(p, writerId) => {
      p.zipWithIndex.foreach{case (regs, readerId) => {
        writeLines(0, "")
        writeLines(1, s"// Registers written by part ${writerId} and read by part ${readerId}")
        regs.foreach{case(typeStr, declName) => {
          writeLines(1, s"${typeStr} ${declName};")
        }}
      }}
      writeLines(1, "// Extra padding to avoid false sharing")
      writeLines(1, s"UInt<512> padding_${writerId};")
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

    writeLines(0, "")

    registerDesc.zipWithIndex.foreach{case(p, writerId) => {
      if (p.nonEmpty) {
        writeLines(0, s"#define PART_${writerId}_DATA_HEAD ${p.head.head._2}")
        writeLines(0, s"#define PART_${writerId}_DATA_LAST ${p.last.last._2}")
      }
    }}

  }



  // Declaring Top level Module. This function is used only by parallel version
  //----------------------------------------------------------------------------
  def declareTopModule(m: Module, c: Circuit, profile: Boolean) {
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
    val modulesAndPrefixes = findAllModuleInstances(c)
    val extModulesAndPrefixes = modulesAndPrefixes.filter{case(modName, _) => {extModuleDict.contains(modName)}}
    val extModuleDecs = extModulesAndPrefixes map { case (module, fullName) => {
      // val instanceName = fullName.split("\\.").last
      val instanceName = fullName.replace('.', '_').dropRight(1)
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
      writeLines(1, s"UInt<512> _padding_${tid * 2};")
      writeLines(1, s"std::atomic<bool> ${gen_thread_eval_token_name(tid)};")
      writeLines(1, s"UInt<512> _padding_${tid * 2 + 1};")
      writeLines(1, s"std::atomic<bool> ${gen_thread_sync_token_name(tid)};")
    }
    writeLines(0, "")
    writeLines(1, s"bool sim_token;")
    writeLines(1, s"UInt<512> _padding_last;")

    if (profile) {
      writeLines(0, "")
      writeLines(1, s"uint64_t cycle_count;")
      writeLines(1, "EssentProfiler* profiler;")
    }

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

    if (profile) {
      writeLines(0, "")
      writeLines(1, s"cycle_count = 0;")
      writeLines(1, "profiler = new EssentProfiler();")
    }

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

    writeLines(0, "")
    if (profile) {
      writeLines(2, "profiler->save(\"profile_exec.dat\");")
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

      if (profile) writeLines(3, s"profiler->record(${tid}, EVENT_CYCLE_START);")


      // call task
      writeLines(3, s"${gen_tp_eval_name(tid)}(update_registers, verbose, done_reset);")
      writeLines(3, s"${gen_thread_eval_token_name(tid)}.store(false);")

      if (profile) writeLines(3, s"profiler->record(${tid}, EVENT_EVAL_DONE);")

      writeLines(3, s"while (${gen_thread_sync_token_name(tid)}.load() == false) {")
      writeLines(4, s"_mm_pause();")
      writeLines(3, "}")


      if (profile) writeLines(3, s"profiler->record(${tid}, EVENT_SYNC_START);")

      writeLines(3, s"${gen_tp_wsync_name(tid)}(update_registers);")
      writeLines(3, s"${gen_thread_sync_token_name(tid)}.store(false);")

      if (profile) writeLines(3, s"profiler->record(${tid}, EVENT_SYNC_DONE);")

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
    writeLines(1, s"} ThreadData_Mem_$pid;")

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
      val memcpy_src = s"reinterpret_cast<char*>(&${getThreadDataName_Reg(pid)}) + offsetof(DesignData, PART_${pid}_DATA_HEAD)"
      val memcpy_dst = s"reinterpret_cast<char*>(&${getGlobalDataName()}) + offsetof(DesignData, PART_${pid}_DATA_HEAD)"
      val memcpy_size = s"offsetof(DesignData, PART_${pid}_DATA_LAST) + sizeof(${getGlobalDataName()}.PART_${pid}_DATA_LAST) - offsetof(DesignData, PART_${pid}_DATA_HEAD)"

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

    def changePrefix(st: String, from: String, to: String) = st.replace(from, to)

    def emitStmt_T(s: Statement)(rn: Renamer) = s match {
      case mw: MemWrite => {
        // Seq(s"if (UNLIKELY(update_registers && ${emitExprWrap(mw.wrEn)(rn)} && ${emitExprWrap(mw.wrMask)(rn)})) ${mw.memName}[${emitExprWrap(mw.wrAddr)(rn)}.as_single_word()] = ${emitExpr(mw.wrData)(rn)};")
        val declName = memNameToDeclName(mw.nodeName())
        Seq(s"${getThreadDataName_Mem(pid)}.${declName}_write_en = ${emitExprWrap(mw.wrEn)(rn)} && ${emitExprWrap(mw.wrMask)(rn)};",
          s"${getThreadDataName_Mem(pid)}.${declName}_index = ${emitExprWrap(mw.wrAddr)(rn)}.as_single_word();",
          s"${getThreadDataName_Mem(pid)}.${declName}_data = ${emitExpr(mw.wrData)(rn)};")
      }

      case ru: RegUpdate => Seq(s"if (update_registers) ${changePrefix(emitExpr(ru.regRef)(rn), "dat.", getThreadDataName_Reg(pid) + ".")} = ${emitExpr(ru.expr)(rn)};")

      case _ => emitStmt(s)(rn)
    }

    // ng.stmtsOrdered foreach { stmt => writeLines(indentLevel, emitStmt(stmt)) }
    if (opt.conditionalMuxes)
      MakeCondMux(sg, rn, keepAvail)
    val noMoreMuxOpts = opt.copy(conditionalMuxes = false)


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
//        writeLines(indentLevel, s"// IR: ${stmt.toString}")
//        writeLines(indentLevel, s"// Serialize: ${stmt.serialize}")
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
    writeLines(0, "#ifdef __x86_64__")
    writeLines(0, "#include <immintrin.h>")
    writeLines(0, "#endif")
    writeLines(0, "#include <array>")
    writeLines(0, "#include <thread>")
    writeLines(0, "#include <atomic>")
    writeLines(0, "#include <cstdint>")
    writeLines(0, "#include <cstdlib>")
    writeLines(0, "#include <uint.h>")
    writeLines(0, "#include <sint.h>")

    writeLines(0, "#ifndef __x86_64__")
    writeLines(0, "void _mm_pause() {};")
    writeLines(0, "#endif")

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


    rn.populateFromSG(sg, extIOMap, isParallel = false)

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


    writeLines(0, s"} $topName;") //closing top module dec
    writeLines(0, "")
    writeLines(0, s"#endif  // $headerGuardName")
  }

  // General Structure (and Compiler Boilerplate)
  //----------------------------------------------------------------------------
  def execute_parallel(circuit: Circuit, sg: StatementGraph, tp: ThreadPartitioner, profile: Boolean) {
    val opt = initialOpt
    val topName = circuit.main
    val headerGuardName = topName.toUpperCase + "_H_"
    writeLines(0, s"#ifndef $headerGuardName")
    writeLines(0, s"#define $headerGuardName")
    writeLines(0, "")
    writeLines(0, "#ifdef __x86_64__")
    writeLines(0, "#include <immintrin.h>")
    writeLines(0, "#endif")
    writeLines(0, "#include <array>")
    writeLines(0, "#include <thread>")
    writeLines(0, "#include <atomic>")
    writeLines(0, "#include <cstdint>")
    writeLines(0, "#include <cstdlib>")
    writeLines(0, "#include <uint.h>")
    writeLines(0, "#include <sint.h>")

    if (profile) {
      writeLines(0, "#include <chrono>")
      writeLines(0, "#include <algorithm>")
      writeLines(0, "#include <fstream>")
      writeLines(0, "")

      writeLines(0, s"#define MAX_PROFILE_CYCLES ${opt.profile_cycles}")
      writeLines(0, s"#define NUM_THREADS ${opt.parallel}")
      val profile_code = """
                           |
                           |
                           |#if defined(__i386__) || defined(__x86_64__)
                           |#define VL_GET_CPU_TICK(val) \
                           |    { \
                           |        uint32_t hi; \
                           |        uint32_t lo; \
                           |        asm volatile("rdtsc" : "=a"(lo), "=d"(hi)); \
                           |        (val) = ((uint64_t)lo) | (((uint64_t)hi) << 32); \
                           |    }
                           |#elif defined(__aarch64__)
                           |# define VL_GET_CPU_TICK(val) \
                           |    { \
                           |        asm volatile("isb" : : : "memory"); \
                           |        asm volatile("mrs %[rt],CNTVCT_EL0" : [rt] "=r"(val)); \
                           |    }
                           |#else
                           |#error "Unsupported platform"
                           |#endif
                           |
                           |inline uint64_t get_tick() {
                           |    uint64_t val;
                           |    VL_GET_CPU_TICK(val);
                           |    return val;
                           |}
                           |
                           |enum ProfileEvent {
                           |    EVENT_CYCLE_START = 0,
                           |    EVENT_EVAL_DONE = 1,
                           |    EVENT_SYNC_START = 2,
                           |    EVENT_SYNC_DONE = 3,
                           |    EVENT_CYCLE_DONE = 4,
                           |};
                           |
                           |#define EVENT_CNT 5
                           |
                           |typedef struct ProfileData
                           |{
                           |    uint64_t time_tick;
                           |}ProfileData;
                           |
                           |
                           |class EssentProfiler {
                           |private:
                           |    ProfileData * data;
                           |    std::atomic<uint64_t> current_cycle;
                           |
                           |    std::chrono::high_resolution_clock::time_point start_time, end_time;
                           |
                           |public:
                           |    EssentProfiler() {
                           |        // Layout:
                           |        // data: Thread 0, Thread 1, ...,
                           |        // Thread n: Event 0, Event 1, ...
                           |        // Event n: cycle 0, cycle 1, ...
                           |        data = new ProfileData[NUM_THREADS * EVENT_CNT * MAX_PROFILE_CYCLES];
                           |        current_cycle = 0;
                           |
                           |        start_time = std::chrono::high_resolution_clock::now();
                           |    }
                           |
                           |    void update_cycle(uint64_t cycle) {current_cycle = cycle;};
                           |
                           |    void record(uint32_t thread_id, ProfileEvent event) {
                           |        if (current_cycle >= MAX_PROFILE_CYCLES) {
                           |            // Do nothing if too many data
                           |            return;
                           |        }
                           |        uint64_t location = (EVENT_CNT * MAX_PROFILE_CYCLES * thread_id + int(event) * MAX_PROFILE_CYCLES + current_cycle);
                           |        data[location].time_tick = get_tick();
                           |    }
                           |
                           |    void save(const char* filename){
                           |
                           |        // Calculate duration
                           |        end_time = std::chrono::high_resolution_clock::now();
                           |        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
                           |        uint64_t duration_ms = duration.count();
                           |
                           |
                           |        uint64_t profile_cycles = std::min(current_cycle.load(), uint64_t(MAX_PROFILE_CYCLES));
                           |
                           |        std::ofstream ofs (filename, std::ofstream::out);
                           |
                           |        ofs << "// ESSENT Profiler log file, v0.1\n"
                           |            << "Duration(ms): " << duration_ms << "\n"
                           |            << "Cycles: " << current_cycle.load() << "\n"
                           |            << "Profile cycles: " << profile_cycles << "\n"
                           |            << "Threads: " << NUM_THREADS << "\n";
                           |
                           |
                           |        ofs << "// Data layout: EVENT_CYCLE_START, EVENT_EVAL_DONE, EVENT_SYNC_START, EVENT_SYNC_DONE, EVENT_CYCLE_DONE \n";
                           |
                           |        uint64_t start_tick = data[0].time_tick;
                           |        for (size_t thread_id = 0; thread_id < NUM_THREADS; thread_id++)
                           |        {
                           |            uint64_t start_tick_location = (EVENT_CNT * MAX_PROFILE_CYCLES * thread_id);
                           |            start_tick = std::min(data[start_tick_location].time_tick, start_tick);
                           |        }
                           |
                           |
                           |        for (size_t thread_id = 0; thread_id < NUM_THREADS; thread_id++)
                           |        {
                           |            ofs << "Thread " << thread_id << ":";
                           |
                           |            for (size_t cycle = 0; cycle < profile_cycles; cycle++)
                           |            {
                           |                for (size_t event_id = 0; event_id < EVENT_CNT; event_id++)
                           |                {
                           |                    uint64_t location = (EVENT_CNT * MAX_PROFILE_CYCLES * thread_id + event_id * MAX_PROFILE_CYCLES + cycle);
                           |                    uint64_t raw_tick = data[location].time_tick;
                           |                    ofs << raw_tick - start_tick << ",";
                           |                }
                           |            }
                           |
                           |            ofs << "\n";
                           |        }
                           |
                           |        ofs.flush();
                           |        ofs.close();
                           |    };
                           |};""".stripMargin
      writeLines(0, profile_code)
      writeLines(0, "")
    }

    writeLines(0, "#ifndef __x86_64__")
    writeLines(0, "void _mm_pause() {};")
    writeLines(0, "#endif")

    writeLines(0, "#define UNLIKELY(condition) __builtin_expect(static_cast<bool>(condition), 0)")
    if (opt.trackParts || opt.trackSigs) {
      writeLines(0, "#include <fstream>")
      writeLines(0, "#include \"../SimpleJSON/json.hpp\"")
      writeLines(0, "using json::JSON;")
      writeLines(0, "uint64_t cycle_count = 0;")
    }
//    writeLines(0, "uint64_t debug_cycle_count = 0;")

    val containsAsserts = sg.containsStmtOfType[Stop]()
    val extIOMap = findExternalPorts(circuit)

    rn.populateFromSG(sg, extIOMap, isParallel = true)


    val part_write_stmts = tp.parts_write.map(_.map(sg.idToStmt(_)).toSeq).toSeq
    val part_read_stmts = tp.parts_read.map(_.map(sg.idToStmt(_)).toSeq).toSeq
    declareFlattenSubModule(circuit, part_read_stmts, part_write_stmts)

    circuit.modules foreach {
      case m: ExtModule => declareExtModule(m)
      case _ => Unit
    }

    val topModule = findModule(topName, circuit) match {case m: Module => m}
    declareTopModule(topModule, circuit, profile)

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
        throw new Exception("Parallelization for O3 not supported yet")
        condPartWorker.doOpt(opt.partCutoff)
      } else {
        if (opt.regUpdates)
          OptElideRegUpdates(sg)
      }


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

    if (profile) writeLines(2, "profiler->record(0, EVENT_CYCLE_START);")
    writeLines(2, s"${gen_tp_eval_name(0)}(update_registers, verbose, done_reset);")
    if (profile) writeLines(2, "profiler->record(0, EVENT_EVAL_DONE);")

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
    if (profile) writeLines(2, "profiler->record(0, EVENT_SYNC_START);")
    writeLines(2, s"${gen_tp_wsync_name(0)}(update_registers);")
    if (profile) writeLines(2, "profiler->record(0, EVENT_SYNC_DONE);")

    // Wait sync complete
    for (tid <- 1 to worker_thread_count) {
      writeLines(2, s"while (${gen_thread_sync_token_name(tid)}.load() == true) {")
      writeLines(3, s"_mm_pause();")
      writeLines(2, s"};")
    }

    if (profile) {
      writeLines(2, "cycle_count++;")

      for (tid <- 0 to worker_thread_count) {
        writeLines(2, s"profiler->record(${tid}, EVENT_CYCLE_DONE);")
      }

      writeLines(0, "")
      writeLines(2, "profiler->update_cycle(cycle_count);")
    }

//      writeLines(2, "debug_cycle_count ++;")
//      writeLines(2, "if (debug_cycle_count % 10000 == 0) std::cout << debug_cycle_count << std::endl;")
    writeLines(1, "}")


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

    if (opt.parallel > 1) {

      //    writeLines(0, "uint64_t debug_cycle_count = 0;")
      val sg = StatementGraph(resultState.circuit, opt.removeFlatConnects)
//      logger.info(sg.makeStatsString)
      val pg = PartGraph(sg)
      val tp = ThreadPartitioner(pg, opt)
      tp.doOpt()

      val dutWriter = new FileWriter(new File(opt.outputDir, s"$topName.h"))
      val emitter = new EssentEmitter(opt, dutWriter)
      emitter.execute_parallel(resultState.circuit, sg, tp, profile = false)
      dutWriter.close()

      if (opt.profile_cycles != 0) {
        val dutWriter = new FileWriter(new File(opt.outputDir, s"${topName}_prof.h"))
        val emitter = new EssentEmitter(opt, dutWriter)
        emitter.execute_parallel(resultState.circuit, sg, tp, profile = true)
        dutWriter.close()
      }
    } else {
      val dutWriter = new FileWriter(new File(opt.outputDir, s"$topName.h"))
      val emitter = new EssentEmitter(opt, dutWriter)
      emitter.execute(resultState.circuit)
      dutWriter.close()
    }
  }
}
