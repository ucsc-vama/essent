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

case class Vcd(circuit: Circuit, initopt: OptFlags, writer: Writer, rn: Renamer) {
  val tabs = "  "
  var iden_code_hier = ""
  val opt = initopt
  val topName = circuit.main
  val sg = StatementGraph(circuit, opt.removeFlatConnects)
  val allNamesAndTypes = sg.stmtsOrdered flatMap findStmtNameAndType

  def writeLines(indentLevel: Int, lines: String) {
    writeLines(indentLevel, Seq(lines))
  }

  def writeLines(indentLevel: Int, lines: Seq[String]) {
    lines foreach { s => writer write tabs*indentLevel + s + "\n" }
  }

  def displayNameIdentifierSize(m: Module, topName: String) {

    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    var depth = 0
    var mem_depth = BigInt(1)
    val register_name_identifier = registers flatMap {d: DefRegister => {
      val width = bitWidth(d.tpe)
      val width_l = bitWidth(d.tpe) - 1
      val identifier_code = " !" + d.name
      if(width_l > 0) Seq(s"""outfile << "$$var wire $width $identifier_code ${d.name} [$width_l:0] $$end" << "\\n";""")
      else Seq(s"""outfile << "$$var wire  $width $identifier_code ${d.name} $$end" << "\\n";""")
    }}

    val ports_name_identifier = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq(s"""outfile << "$$var wire "<< " 1 " << " !clock" << " ${p.name} " << " $$end" << "\\n";""")
        case _ =>
          val width = bitWidth(p.tpe)
          val width_l = bitWidth(p.tpe) - 1
          val identifier_code = " !" + p.name
          if(width_l > 0) Seq(s"""outfile << "$$var wire $width $identifier_code ${p.name} [$width_l:0] $$end" << "\\n";""")
          else Seq(s"""outfile << "$$var wire $width $identifier_code ${p.name} $$end" << "\\n";""")
      }}

    if(m.name == topName) {
      writeLines(2, register_name_identifier)
      writeLines(2, ports_name_identifier)
      if(memories.size != 0) {
        while(depth < mem_depth) {
          memories map { m: DefMemory => {
            val width = bitWidth(m.dataType)
            val identifier_code = " !" + m.name + "[" + depth + "]"
            writeLines(2,s"""outfile << "$$var wire "<< " $width " << "$identifier_code " << " ${m.name}[${depth}] " << " $$end" << "\\n";""")
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
      writeLines(1, registerDecs)
      writeLines(1, memDecs)
      writeLines(1, ports_old)
    }
  }

  def compareOldNewSignal(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val regname = d.name
      val regoldname = rn.vcdOldValue(regname)
      Seq(s"""if((cycle_count == 0) || ($regname != $regoldname)) {outfile << $regname.to_bin_str(); outfile << "!$regname" << "\\n";}""")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"""if((cycle_count == 0) || (${m.name}[${m.depth}] != ${rn.vcdOldValue(m.name)}[${m.depth}])) { outfile << ${m.name}[${m.depth}].to_bin_str(); outfile << "!${m.name}[${m.depth}]" << "\\n";}"""
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq()
        case _ =>
          val ports_name = rn.vcdOldValue(p.name) 
          Seq(s"""if((cycle_count == 0) || (${p.name} != $ports_name)) {outfile << ${p.name}.to_bin_str(); outfile << "!${p.name}" << "\\n";}""")
      }}
    if(modName == topName) {
      writeLines(2, registerDecs)
      writeLines(2, memDecs)
      writeLines(2, ports_old)
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
      writeLines(2, "//Assigning old values ")
      writeLines(2, registerDecs)
      writeLines(2, memDecs)
      writeLines(2, ports_old)
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
                val width = bitWidth(tpe)
                writeLines(indentlevel,s"""outfile << "$$var wire $width !${iden_code} $key $$end" << "\\n";""")
              }}
        }
        }}
      else {
        writeLines(indentlevel, s""" outfile << "$$scope module $key $$end" << "\\n";""")
        val iden_code_hier_new = iden_code_hier + key + "$"
        hierScope(allNamesAndTypes,next_non_empty_values,indentlevel,iden_code_hier_new)
        writeLines(indentlevel,""" outfile << "$upscope $end" << "\\n";""")
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
            writeLines(1, s"""${genCppType(tpe)} ${rn.vcdOldValue(new_name)};""")
          }
        }
    }
  }

  def initializeOldValues(circuit: Circuit): Unit = {
    writeLines(1, "if(cycle_count == 0) {")
    writeLines(3, """outfile << "$dumpvars" << "\\n" ;""")
    writeLines(1, " } ")
    writeLines(1, "else { ")
    writeLines(2, """outfile << "#" << cycle_count*10 << "\\n";""")
    writeLines(2, """ outfile << "1" << "!clock" << "\\n";""")
    writeLines(1, " } ")
    }

  def compareOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => compareOldNewSignal(m, topName)
      case m: ExtModule => Seq()
    }
    writeLines(1, "if(cycle_count == 0) {")
    writeLines(3, """outfile << "$end" << "\\n";""")
    writeLines(1, " } ")
    writeLines(2, """outfile << "#" << (cycle_count*10 + 5) << "\\n";""")
    writeLines(2, """ outfile << "0" << "!clock" << "\\n";""")
    writeLines(2, "cycle_count++;")
    writeLines(2, "")
  }

  def assignOldValues(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => assignOldValue(m, topName)
      case m: ExtModule => Seq()
    }
  }

  def genWaveHeader(): Unit = {
    writeLines(1, "void genWaveHeader() {")
    writeLines(0, "")
    writeLines(2, "time_t timetoday;")
    writeLines(2, "time (&timetoday);")
    writeLines(2, """outfile << "$version Essent version 1 $end" << "\\n";""")
    writeLines(2, """outfile << "$date " << asctime(localtime(&timetoday)) << " $end" << "\\n";""")
    writeLines(2, """outfile << "$timescale 1ns $end" << "\\n";""")
    writeLines(2, s"""outfile << "$$scope module " << "$topName" << " $$end" << "\\n";""")
    circuit.modules foreach {
      case m: Module => displayNameIdentifierSize(m, topName)
      case m: ExtModule => Seq()
    }
    val name = sg.stmtsOrdered flatMap findResultName
    val non_und_name = name map { n => if (!n.contains("._") && !n.contains("$next") && n.contains(".")) n else "" }
    val splitted = non_und_name map { _.split('.').toSeq}
    hierScope(allNamesAndTypes, splitted,2,iden_code_hier)
    writeLines(2, """outfile << "$upscope $end " << "\\n";""")
    writeLines(2, """outfile << "$enddefinitions $end" << "\\n";""")
    writeLines(0, "")
    writeLines(1, "}")
    writeLines(0, "")
  }
}
