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

case class EssentVcd(circuit: Circuit, initopt: OptFlags, writer: Writer, rn: Renamer) {
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

  def declareoldvalues(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val typeStr = genCppType(d.tpe)
      val regname = d.name
      val regoldname = s"${regname}_old"
      Seq(s"$typeStr $regoldname;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${genCppType(m.dataType)} ${m.name}_old[${m.depth}];"
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq(genCppType(UIntType(IntWidth(1))) + " " + p.name + "_old" +";")
        case _ =>
          val ports_name = s"${p.name}_old"
          val type_port = genCppType(p.tpe)
          Seq(s"$type_port $ports_name;")
      }
    }
    if(modName == topName) {
      writeLines(1, "//declaring old values for vcd generation")
      writeLines(1, registerDecs)
      writeLines(1, memDecs)
      writeLines(1, ports_old)
    }
  }

  def initializeSignal(m: Module, topName: String) {

    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val regname = d.name
      Seq(s"""outfile << $regname.to_bin_str(); outfile << "!${regname}" << "\\n";""")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"""outfile << ${m.name}[${m.depth}].to_bin_str(); outfile << "!${m.name}[${m.depth}]" << "\\n";"""
    }}
    val modName = m.name
    val ports_values = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq(s"""outfile << ${p.name}.to_bin_str(); outfile << "!${p.name}" << "\\n";""")
        case _ =>
          Seq(s"""outfile << ${p.name}.to_bin_str(); outfile << "!${p.name}" << "\\n";""")
      }}
    if(modName == topName) {
      writeLines(3, "//Initializing values ")
      writeLines(3, registerDecs)
      writeLines(3, memDecs)
      writeLines(3, ports_values)
    }
  }

  def compareOldNewSignal(m: Module, topName: String) {
    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val regname = d.name
      val regoldname = s"${regname}_old"
      Seq(s"""if($regname != $regoldname) {outfile << $regname.to_bin_str(); outfile << "!$regname" << "\\n";}""")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"""if(${m.name}[${m.depth}] != ${m.name}_old[${m.depth}]) { outfile << ${m.name}[${m.depth}].to_bin_str(); outfile << "!${m.name}[${m.depth}]" << "\\n";}"""
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      p.tpe match {
        case ClockType => Seq(s"""if(${p.name} != ${p.name}_old) {outfile << ${p.name}.to_bin_str(); outfile << "!${p.name}" << "\\n";}""")
        case _ =>
          val ports_name = s"${p.name}_old"
          Seq(s"""if(${p.name} != $ports_name) {outfile << ${p.name}.to_bin_str(); outfile << "!${p.name}" << "\\n";}""")
      }}
    if(modName == topName) {
      writeLines(2, "//Comparing old and new values for vcd data section")
      writeLines(2, registerDecs)
      writeLines(2, memDecs)
      writeLines(2, ports_old)
    }
  }

  def assignOldValues(m: Module, topName: String) {

    val registers = findInstancesOf[DefRegister](m.body)
    val memories = findInstancesOf[DefMemory](m.body)
    val registerDecs = registers flatMap {d: DefRegister => {
      val regname = d.name
      val regoldname = s"${regname}_old"
      Seq(s"$regoldname = $regname;")
    }}
    val memDecs = memories map {m: DefMemory => {
      s"${m.name}_old[${m.depth}] = ${m.name}[${m.depth}];"
    }}
    val modName = m.name
    val ports_old = m.ports flatMap { p =>
      //Removing signal names with "_" similar to verilator
      if(p.name.contains("$_")) {
        Seq()
      }
      else {
        p.tpe match {
          case ClockType => Seq(s"${p.name}_old = ${p.name};")
          case _ =>
            val ports_name = s"${p.name}_old"
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
  def hier_scope(allNamesAndTypes: Seq[(String, Type)],splitted: Seq[Seq[String]], indentlevel: Int, iden_code_hier: String) {

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
              val new_name = name.replace(".","$")
              if(new_name == iden_code) {
                val width = bitWidth(tpe)
                writeLines(indentlevel,s"""outfile << "$$var wire $width !${iden_code} $key $$end" << "\\n";""")
              }}
        }
        }}
      else {
        writeLines(indentlevel, s""" outfile << "$$scope module $key $$end" << "\\n";""")
        val iden_code_hier_new = iden_code_hier + key + "$"
        hier_scope(allNamesAndTypes,next_non_empty_values,indentlevel+1,iden_code_hier_new)
        writeLines(indentlevel,s""" outfile << "$$upscope $$end" << "\\n";""")
      }
    }
    }
  }

  def declareoldvalues_all(circuit: Circuit): Unit = {
    circuit.modules foreach {
      case m: Module => declareoldvalues(m, topName)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
          val new_name = name.replace('.','$')
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
            writeLines(1, s"""${genCppType(tpe)} ${new_name}_old;""")
          }
        }
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
          val new_name = name.replace('.','$')
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
          writeLines(1, s"""${genCppType(tpe)} ${new_name};""")
        }
      }
    }
  }

  def initialize_compare_assign_old_values(circuit: Circuit): Unit = {
    writeLines(1, "if(cycle_count == 0) {")
    writeLines(3, s"""outfile << \"$$dumpvars\" << "\\n" ;""")
    circuit.modules foreach {
      case m: Module => initializeSignal(m, topName)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO && rn.nameToMeta(name).decType != RegSet) {
          val new_name = name.replace('.','$')
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
            writeLines(3, s"""outfile << ${new_name}.to_bin_str(); outfile << "!${new_name}" << "\\n";""")
          }
        }
    }
    writeLines(3, s"""outfile << \"$$end\" << "\\n";""")
    writeLines(1, " } ")
    writeLines(2, s"""outfile << \"#\" << cycle_count*10 << "\\n";""")

    writeLines(2, s""" outfile << "1" << "!clock" << "\\n";""")
    circuit.modules foreach {
      case m: Module => compareOldNewSignal(m, topName)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO  && rn.nameToMeta(name).decType != RegSet) {
          val new_name = name.replace('.','$')
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
            writeLines(2, s"""if(${new_name} != ${new_name}_old ) { outfile << ${new_name}.to_bin_str(); outfile << "!${new_name}" << "\\n";}""")
          }
        }
    }
    writeLines(2, s"""outfile << \"#\" << (cycle_count*10 + 5) << "\\n";""")
    writeLines(2, s""" outfile << "0" << "!clock" << "\\n";""")
    writeLines(2, "cycle_count++;")
    writeLines(2, "")
    circuit.modules foreach {
      case m: Module => assignOldValues(m, topName)
      case m: ExtModule => Seq()
    }
    allNamesAndTypes map {
      case(name, tpe) =>
        if(rn.nameToMeta(name).decType != ExtIO  && rn.nameToMeta(name).decType != RegSet) {
          val new_name = name.replace('.','$')
          if(!new_name.contains("$_") && !new_name.contains("$next") && !new_name.startsWith("_")) {
            writeLines(2, s"""${new_name}_old = ${new_name};""")
          }
        }
    }
  }

  def genWaveHeader(): Unit = {
    writeLines(1, s"void genWaveHeader() {")
    writeLines(0, "")
    writeLines(2, s"time_t timetoday;")
    writeLines(2, s"time (&timetoday);")
    writeLines(2, s"""outfile << \"$$version Essent version 1 $$end\" << "\\n";""")
    writeLines(2, s"""outfile << \"$$date \" << asctime(localtime(&timetoday)) << \" $$end\" << "\\n";""")
    writeLines(2, s"""outfile << \"$$timescale 1ns $$end\" << "\\n";""")
    writeLines(2, s"""outfile << "$$scope module " << "$topName" << " $$end" << "\\n";""")
    circuit.modules foreach {
      case m: Module => displayNameIdentifierSize(m, topName)
      case m: ExtModule => Seq()
    }
    val name = sg.stmtsOrdered flatMap findStmtName
    //val name = sg.nameToID.keys ( not producing same result as above )
    val non_und_name = name map { n => if (!n.contains("._") && !n.contains("$next") && n.contains(".")) n else "" }
    val splitted = non_und_name map { _.split('.').toSeq}
    //hier_scope(allNamesAndTypes, splitted.toSeq,2,iden_code_hier)
    hier_scope(allNamesAndTypes, splitted,2,iden_code_hier)
    writeLines(2, s"""outfile << \"$$upscope $$end \" << "\\n";""")
    writeLines(2, s"""outfile << \"$$enddefinitions $$end\" << "\\n";""")
    writeLines(0, "")
    writeLines(1, "}")
    writeLines(0, "")
  }
}
