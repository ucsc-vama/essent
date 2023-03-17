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
  val allNamesAndTypes = sg.stmtsOrdered flatMap findStmtNameAndType
  var hashMap =  HashMap[String,String]() 
  var last_used_index = BigInt(1)

  def displayNameIdentifierSize(m: Module, topName: String) {

    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    var depth = 0
    var mem_depth = BigInt(1)
    val register_name_identifier = registers flatMap {d: DefRegister => {
      val width = bitWidth(d.tpe)
      val width_l = bitWidth(d.tpe) - 1
      val identifier_code = genIdenCode(last_used_index)
      last_used_index = last_used_index + 1
      hashMap(d.name) = identifier_code
      if(width_l > 0) Seq(s""" "%s","$$var wire $width $identifier_code ${d.name} [$width_l:0] $$end\\n");""")
      else Seq(s""" "%s","$$var wire  $width $identifier_code ${d.name} $$end\n");""")
    }}

    val ports_name_identifier = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq(s""" "%s","$$var wire 1  !clock ${p.name}  $$end\\n");""")
        case _ =>
          val width = bitWidth(p.tpe)
          val width_l = bitWidth(p.tpe) - 1
          val identifier_code = genIdenCode(last_used_index)
          last_used_index = last_used_index + 1
          hashMap(p.name) = identifier_code
          if(width_l > 0) Seq(s""" "%s","$$var wire $width $identifier_code ${p.name} [$width_l:0] $$end\\n");""")
          else Seq(s""" "%s","$$var wire $width $identifier_code ${p.name} $$end\\n");""")
      }}

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
            writeFprintf(s""" "%s","$$var wire $width $identifier_code ${m.name}[${depth}] $$end\\n");""")
            depth = depth + 1
            mem_depth = m.depth
          }
          }
        }
      }
    }
  }

  def declareOldValues(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regoldname = rn.vcdOldValue(d.name)
      Seq(s"$typeStr $regoldname;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${rn.vcdOldValue(m.name)}[${m.depth}];"
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq()
        case _ =>
          val ports_name = rn.vcdOldValue(p.name) 
          val type_port = genCppType(p.tpe)
          Seq(s"$type_port $ports_name;")
      }
    }
    if(modName == topName) {
      w.writeLines(1, registerDecs)
      w.writeLines(1, memDecs)
      w.writeLines(1, ports_old)
    }
  }

  def compareOldNewSignal(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val temp_string = compSig(d.name,rn.vcdOldValue(d.name))
      Seq(temp_string)
    }}
    val ports_old = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq()
        case _ =>
      val temp_string = compSig(p.name,rn.vcdOldValue(p.name))
      Seq(temp_string)
      }}
    val modName = m.name
    if(modName == topName) {
    val memDecs = memories map {m: DefMemory => {
      compSig(s"""${m.name}[${m.depth}]""",s"""${rn.vcdOldValue(m.name)}[${m.depth}]""")
    }}
    w.writeLines(2, registerDecs)
    w.writeLines(2, memDecs)
    w.writeLines(2, ports_old)
    }
  }

  def assignOldValue(m: Module, topName: String) {

    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val regname = d.name
      val regoldname = rn.vcdOldValue(regname) 
      Seq(s"$regoldname = $regname;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${rn.vcdOldValue(m.name)}[${m.depth}] = ${m.name}[${m.depth}];"
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      //Removing signal names with "_" similar to verilator
      if(p.name.contains("$_")) {
        Seq()
      }
      else {
        p.tpe match {
          case ClockType => Seq()
          case _ =>
            val ports_name = rn.vcdOldValue(p.name)
            Seq(s"$ports_name = ${p.name};")
        }}}
    if(modName == topName) {
      w.writeLines(2, "//Assigning old values ")
      w.writeLines(2, registerDecs)
      w.writeLines(2, memDecs)
      w.writeLines(2, ports_old)
    }
  }

  //function for vcd multiple hierarchy
  def hierScope(allNamesAndTypes: Seq[(String, Type)],splitted: Seq[Seq[String]], indentlevel: Int, iden_code_hier: String) {

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
                writeFprintf(s""" "%s","$$var wire $width ${ident_code} $key $$end\\n");""")
              }}
        }
        }}
      else {
        writeFprintf(s""" "%s","$$scope module $key $$end\\n");""")
        val iden_code_hier_new = iden_code_hier + key + "$"
        hierScope(allNamesAndTypes,next_non_empty_values,indentlevel,iden_code_hier_new)
        writeFprintf(""" "%s","$upscope $end\n");""")
      }
    }
    }
  }

  def declareOldvaluesAll(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => declareOldValues(m, topName)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
          val new_name = rn.removeDots(name)
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
            w.writeLines(1, s"""${genCppType(tpe)} ${rn.vcdOldValue(new_name)};""")
          }
        }
    }
  }

  def initializeOldValues(circuit: Circuit): Unit = {
    w.writeLines(1, "if(vcd_cycle_count == 0) {")
    writeFprintf(""" "%s","$dumpvars\n");""")
    w.writeLines(1, " } ")
    w.writeLines(1, "else { ")
    writeFprintf(""" "%s%s%s","#",std::to_string(vcd_cycle_count*10).c_str(),"\n");""")
    writeFprintf(""" "%s","1!clock\n");""")
    w.writeLines(1, " } ")
    }

  def compareOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => compareOldNewSignal(m, topName)
      case m: ExtModule => Seq()
    }
    w.writeLines(1, "if(vcd_cycle_count == 0) {")
    writeFprintf(""" "%s","$end\n");""")
    w.writeLines(1, " } ")
    writeFprintf(""" "%s%s%s","#",std::to_string(vcd_cycle_count*10 + 5).c_str(),"\n");""")
    writeFprintf(""" "%s","0!clock\n");""")
    w.writeLines(2, "vcd_cycle_count++;")
    w.writeLines(2, "")
  }

  def assignOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => assignOldValue(m, topName)
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
    writeFprintf(""" "%s","$version Essent version 1 $end\n");""")
    writeFprintf(""" "%s%s%s","$date ",asctime(localtime(&timetoday))," $end\n");""")
    writeFprintf(""" "%s","$timescale 1ns $end\n");""")
    writeFprintf(s""" "%s","$$scope module $topName $$end\\n");""")
    circuit.modules foreach {
      case m: Module => displayNameIdentifierSize(m, topName)
      case m: ExtModule => Seq()
    }
    val name = sg.stmtsOrdered flatMap findResultName
    val debug_name = name map { n => if ( !n.contains(".")) n else ""}
      var up_index = last_used_index
    debug_name.zipWithIndex map { case(sn, index ) => {
      val iden_code = genIdenCode(index + last_used_index)
      val sig_name = rn.removeDots(sn)
      if ( !hashMap.contains(sig_name)) {
      hashMap(sig_name) = iden_code
      up_index = index + last_used_index}
    }}
    last_used_index = up_index 
    val non_und_name = name map { n => if (!n.contains("._") && !n.contains("$next") && n.contains(".")) n else "" }
    val splitted = non_und_name map { _.split('.').toSeq}
    non_und_name.zipWithIndex map { case(sn , index ) => {
          val sig_name = rn.removeDots(sn)
          val iden_code = genIdenCode(index + last_used_index)
          hashMap(sig_name) = iden_code
        }
        }
    hierScope(allNamesAndTypes, splitted,2,iden_code_hier)
    writeFprintf(""" "%s","$upscope $end\n");""")
    writeFprintf(""" "%s","$enddefinitions $end\n");""")
    w.writeLines(0, "")
    w.writeLines(1, "}")
    w.writeLines(0, "")
  }

  def writeFprintf(s: String) {
  w.writeLines(2,s"""fprintf(outfile,$s""")
  }

  def compSig(sn: String,on: String): String = {
      val iden_code = hashMap(sn)
      s"""if((vcd_cycle_count == 0) || ($sn != $on)) {fprintf(outfile,"%s",$sn.to_bin_str().c_str()); fprintf(outfile,"%s","$iden_code\\n");}"""
  }

  def genIdenCode(i: BigInt): String = {
     var iden_code = ""
     var v = i
     while (v != 0) {
       v = v - 1;
       val eq_char = ((v%94) + 33).toChar
       if((eq_char == '\"') || (eq_char == '\\') || (eq_char == '?'))
         iden_code = iden_code + "\\" + eq_char
       else 
         iden_code = iden_code + eq_char
       v = v/94;
        }
      iden_code
  }

   def compSmallEval(stmt: Statement, indentLevel: Int): Unit = {
       stmt match {
         case mw: MemWrite =>
         case _ =>
           val resultName = findResultName(stmt)
            resultName match {
              case Some(name) =>
                 val cleanName = rn.removeDots(name)
                  if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
                    if(!cleanName.contains("$_") && !cleanName.contains("$next") && !cleanName.startsWith("_")) {
                      val temp_str = compSig(cleanName,rn.vcdOldValue(cleanName))
                      w.writeLines(indentLevel, temp_str)
                       w.writeLines(indentLevel, s""" ${rn.vcdOldValue(cleanName)} = $cleanName;""")
                    }
                  }
              case None =>
            }
       }

   }
  
}

