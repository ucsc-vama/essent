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
import collection.mutable.HashMap

class Vcd(circuit: Circuit, initopt: OptFlags, w: Writer, rn: Renamer) {
  var iden_code_hier = ""
  val opt = initopt
  val topName = circuit.main
  val sg = StatementGraph(circuit, opt.removeFlatConnects)
  val allNamesAndTypes = sg.stmtsOrdered() flatMap findStmtNameAndType
  var hashMap =  HashMap[String,String]() 
  var last_used_index = BigInt(1)

  def displayNameIdentifierSize(m: Module, topName: String): Unit = {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    var depth = 0
    var mem_depth = BigInt(1)
    val register_name_identifier = registers map {d: DefRegister =>
      val width = bitWidth(d.tpe)
      val width_l = bitWidth(d.tpe) - 1
      val identifier_code = genIdenCode(last_used_index)
      last_used_index = last_used_index + 1
      hashMap(d.name) = identifier_code
      if (width_l > 0) s""""$$var wire $width $identifier_code ${d.name} [$width_l:0] $$end\\n""""
      else s""""$$var wire  $width $identifier_code ${d.name} $$end\n""""
    }

    val ports_name_identifier = m.ports map { p =>
      p.tpe match {
        case ClockType => s""""$$var wire 1  !clock ${p.name}  $$end\\n""""
        case _ =>
          val width = bitWidth(p.tpe)
          val width_l = bitWidth(p.tpe) - 1
          val identifier_code = genIdenCode(last_used_index)
          last_used_index = last_used_index + 1
          hashMap(p.name) = identifier_code
          if (width_l > 0) s""""$$var wire $width $identifier_code ${p.name} [$width_l:0] $$end\\n""""
          else s""""$$var wire $width $identifier_code ${p.name} $$end\\n""""
      }
    }

    if(m.name == topName) {
      register_name_identifier.foreach(writeFprintf(_))
      ports_name_identifier.foreach(writeFprintf(_))
      if(memories.size != 0) {
        while(depth <= mem_depth) {
          memories map { m: DefMemory => {
            val width = bitWidth(m.dataType)
            val mem_name = m.name + "[" + depth + "]"
            val identifier_code = genIdenCode(last_used_index)
            last_used_index = last_used_index + 1
            hashMap(mem_name) = identifier_code
            writeFprintf(s""""$$var wire $width $identifier_code ${m.name}[${depth}] $$end\\n"""")
            depth = depth + 1
            mem_depth = m.depth
          }}
        }
      }
    }
  }

  def declareOldValues(m: Module): Unit = {
    val registers = findInstancesOf[DefRegister](m.body)
    val registerDecs = registers map {
      r: DefRegister => s"${genCppType(r.tpe)} ${rn.vcdOldValue(r.name)};"
    }
    val memories = findInstancesOf[DefMemory](m.body)
    val memDecs = memories map { m: DefMemory =>
      s"${genCppType(m.dataType)} ${rn.vcdOldValue(m.name)}[${m.depth}];"
    }
    val portDecs = m.ports collect {
      case p if (p.tpe != ClockType) => s"${genCppType(p.tpe)} ${rn.vcdOldValue(p.name)};"
    }
    w.writeLines(1, registerDecs)
    w.writeLines(1, memDecs)
    w.writeLines(1, portDecs)
  }

  def compareOldNewSignal(m: Module): Unit = {
    val registers = findInstancesOf[DefRegister](m.body)
    val registerComps = registers map {
      r: DefRegister => compSig(r.name, rn.vcdOldValue(r.name))
    }
    val memories = findInstancesOf[DefMemory](m.body)
    val memComps = memories map { m: DefMemory =>
      // TODO: Is this correct?
      compSig(s"${m.name}[${m.depth}]", s"${rn.vcdOldValue(m.name)}[${m.depth}]")
    }
    val portComps = m.ports collect {
      case p if (p.tpe != ClockType) => compSig(p.name, rn.vcdOldValue(p.name))
    }
    w.writeLines(2, registerComps)
    w.writeLines(2, memComps)
    w.writeLines(2, portComps)
  }

  def assignOldValue(m: Module): Unit = {
    val registers = findInstancesOf[DefRegister](m.body)
    val registerAssigns = registers map {
      r: DefRegister => s"${rn.vcdOldValue(r.name)} = ${r.name};"
    }
    val memories = findInstancesOf[DefMemory](m.body)
    val memAssigns = memories map { m: DefMemory =>
      // TODO: Is this correct?
      s"${rn.vcdOldValue(m.name)}[${m.depth}] = ${m.name}[${m.depth}];"
    }
    // Removing signal names with "_" similar to verilator
    val portAssigns = m.ports collect {
      case p if (!p.name.contains("$_") && p.tpe != ClockType) =>
        s"${rn.vcdOldValue(p.name)} = ${p.name};"
    }    
    w.writeLines(2, "//Assigning old values ")
    w.writeLines(2, registerAssigns)
    w.writeLines(2, memAssigns)
    w.writeLines(2, portAssigns)
  }

  //function for vcd multiple hierarchy
  def hierScope(allNamesAndTypes: Seq[(String, Type)],splitted: Seq[Seq[String]], indentlevel: Int, iden_code_hier: String): Unit = {

    // This groups returns a Map( key -> Seq[Seq[String]]
    val grouped = splitted groupBy {_.head }
    grouped foreach { case (key, value) => {
      val next_values = value map {_.tail}
      val next_non_empty_values = next_values.filter(_.nonEmpty)
      val uni_value = value.distinct
      if(uni_value.size == 1) {
        value foreach { v => if(v.size == 1) {
          val iden_code = iden_code_hier + key
          allNamesAndTypes map {
            case (name , tpe ) =>
              val new_name = rn.removeDots(name)
              if(new_name == iden_code) {
                val ident_code = hashMap(new_name)
                val width = bitWidth(tpe)
                writeFprintf(s""""$$var wire $width ${ident_code} $key $$end\\n"""")
              }}
        }
        }}
      else {
        writeFprintf(s""""$$scope module $key $$end\\n"""")
        val iden_code_hier_new = iden_code_hier + key + "$"
        hierScope(allNamesAndTypes,next_non_empty_values,indentlevel,iden_code_hier_new)
        writeFprintf(""""$upscope $end\n"""")
      }
    }}
  }

  def localSignalToTrack(name: String): Boolean = {
    val isLocal = rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet
    val new_name = rn.removeDots(name)
    val safeToWrite = !new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")
    isLocal && safeToWrite
  }

  def declareOldvaluesAll(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => if (m.name == topName) declareOldValues(m)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes foreach { case(name, tpe) =>
      if (localSignalToTrack(name))
        w.writeLines(1, s"""${genCppType(tpe)} ${rn.vcdOldValue(rn.removeDots(name))};""")
    }
  }

  def initializeOldValues(circuit: Circuit): Unit = {
    w.writeLines(1, "if(vcd_cycle_count == 0) {")
    writeFprintf(""""$dumpvars\n"""")
    w.writeLines(1, " } ")
    w.writeLines(1, "else { ")
    writeFprintf(""" "#%s\n", std::to_string(vcd_cycle_count*10).c_str()""")
    writeFprintf(""""1!clock\n"""")
    w.writeLines(1, " } ")
  }

  def compareOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => if (m.name == topName) compareOldNewSignal(m)
      case m: ExtModule => Seq()
    }
    w.writeLines(1, "if(vcd_cycle_count == 0) {")
    writeFprintf(""""$end\n"""")
    w.writeLines(1, " } ")
    writeFprintf(""" "#%s\n", std::to_string(vcd_cycle_count*10 + 5).c_str()""")
    writeFprintf(""""0!clock\n"""")
    w.writeLines(2, "vcd_cycle_count++;")
    w.writeLines(2, "")
  }

  def assignOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => if (m.name == topName) assignOldValue(m)
      case m: ExtModule => Seq()
    }
  }

  def genWaveHeader(): Unit = {
    w.writeLines(1, "void genWaveHeader() {")
    w.writeLines(0, "")
    if(opt.withFST) 
      w.writeLines(1,s"""outfile = fopen("/dev/stdout","w+");""") 
    else 
      w.writeLines(1,s"""outfile = fopen("dump_$topName.vcd","w+");""") 
    w.writeLines(2, "time_t timetoday;")
    w.writeLines(2, "time (&timetoday);")
    writeFprintf(""""$version Essent version 1 $end\n"""")
    writeFprintf(""""$date %s $end\n", asctime(localtime(&timetoday))""")
    writeFprintf(""""$timescale 1ns $end\n"""")
    writeFprintf(s""""$$scope module $topName $$end\\n"""")
    circuit.modules foreach {
      case m: Module => displayNameIdentifierSize(m, topName)
      case m: ExtModule => Seq()
    }
    val name = sg.stmtsOrdered() flatMap findResultName
    val debug_name = name map { n => if ( !n.contains(".")) n else ""}
    var up_index = last_used_index
    debug_name.zipWithIndex foreach { case(sn, index ) => {
      val iden_code = genIdenCode(index + last_used_index)
      val sig_name = rn.removeDots(sn)
      if ( !hashMap.contains(sig_name)) {
      hashMap(sig_name) = iden_code
      up_index = index + last_used_index}
    }}
    last_used_index = up_index 
    val non_und_name = name map { n => if (!n.contains("._") && !n.contains("$next") && n.contains(".")) n else "" }
    val splitted = non_und_name map { _.split('.').toSeq}
    non_und_name.zipWithIndex foreach { case(sn , index ) => {
      val sig_name = rn.removeDots(sn)
      val iden_code = genIdenCode(index + last_used_index)
      hashMap(sig_name) = iden_code
    }}
    hierScope(allNamesAndTypes, splitted,2,iden_code_hier)
    writeFprintf(""""$upscope $end\n"""")
    writeFprintf(""""$enddefinitions $end\n"""")
    w.writeLines(0, "")
    w.writeLines(1, "}")
    w.writeLines(0, "")
  }

  def writeFprintf(s: String): Unit = {
    w.writeLines(2,s"fprintf(outfile,$s);")
  }

  def sanitizeIdenCode(idenCode: String): String = {
    idenCode flatMap {
      case '%' => "%%"
      case '\\' => "\\\\"
      case '"' => "\\\""
      case c => c.toString
    }
  }

  def compSig(sn: String,on: String): String = {
    s"""if((vcd_cycle_count == 0) || ($sn != $on)) {fprintf(outfile,"%s${hashMap(sn)}\\n",$sn.write_char_buf(VCD_BUF));}"""
  }

  def genIdenCode(i: BigInt): String = {
     var iden_code = ""
     var v = i
     while (v != 0) {
       v = v - 1;
       val eq_char = ((v%94) + 33).toChar
       // if((eq_char == '\"') || (eq_char == '\\') || (eq_char == '?'))
       //   iden_code = iden_code + "\\" + eq_char
       // else
       iden_code = iden_code + eq_char
       v = v/94;
     }
     sanitizeIdenCode(iden_code)
  }

  def compSmallEval(stmt: Statement, indentLevel: Int): Unit = stmt match {
    case mw: MemWrite =>
    case _ => findResultName(stmt) match {
      case Some(name) =>
        val cleanName = rn.removeDots(name)
        if (localSignalToTrack(name)) {
          val temp_str = compSig(cleanName,rn.vcdOldValue(cleanName))
          w.writeLines(indentLevel, temp_str)
          w.writeLines(indentLevel, s""" ${rn.vcdOldValue(cleanName)} = $cleanName;""")
        }
      case None =>
    }
  }
}
