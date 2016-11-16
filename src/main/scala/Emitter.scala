package essent

import essent.Extract._

import firrtl._
import firrtl.Annotations._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes.bitWidth
import firrtl.PrimOps._
import firrtl.Utils._

import util.Random

object Emitter {
  case class HyperedgeDep(name: String, deps: Seq[String], stmt: Statement)

  // Declaration Methods
  def genCppType(tpe: Type) = tpe match {
    case UIntType(IntWidth(w)) => {
      if (w <= 64) "uint64_t"
      else "mpz_class"
    }
    case SIntType(IntWidth(w)) => {
      if (w <= 64) "int64_t"
      else "mpz_class"
    }
    case _ => throw new Exception(s"No CPP type implemented for $tpe")
  }

  def genMask(tpe: Type): String = tpe match {
    case gt: GroundType => {
      val width = bitWidth(tpe).toInt
      val maskValue = (BigInt(1) << width) - 1
      if (width > 64) s"""mpz_class("${maskValue.toString(16)}", 16)"""
      else s"0x${maskValue.toString(16)}"
    }
  }


  // Replacement methods
  def addPrefixToNameStmt(prefix: String)(s: Statement): Statement = {
    val replaced = s match {
      case n: DefNode => DefNode(n.info, prefix + n.name, n.value)
      case _ => s
    }
    replaced map addPrefixToNameStmt(prefix) map addPrefixToNameExpr(prefix)
  }

  def addPrefixToNameExpr(prefix: String)(e: Expression): Expression = {
    val replaced = e match {
      case w: WRef => WRef(prefix + w.name, w.tpe, w.kind, w.gender)
      case _ => e
    }
    replaced map addPrefixToNameExpr(prefix)
  }

  def findRootKind(e: Expression): Kind = e match {
    case w: WRef => w.kind
    case w: WSubField => findRootKind(w.exp)
  }

  def replaceNamesStmt(renames: Map[String, String])(s: Statement): Statement = {
    val nodeReplaced = s match {
      case n: DefNode => {
        if (renames.contains(n.name)) DefNode(n.info, renames(n.name), n.value)
        else n
      }
      case _ => s
    }
    nodeReplaced map replaceNamesStmt(renames) map replaceNamesExpr(renames)
  }

  def replaceNamesExpr(renames: Map[String, String])(e: Expression): Expression = e match {
    case w: WRef => {
      if (renames.contains(w.name)) WRef(renames(w.name), w.tpe, w.kind, w.gender)
      else w
    }
    case w: WSubField => {
      val fullName = emitExpr(w)
      if (renames.contains(fullName)) WRef(renames(fullName), w.tpe, findRootKind(w), w.gender)
      else w
    }
    case _ => e map replaceNamesExpr(renames)
  }


  // Helper methods for building eval bodies
  def grabMemInfo(s: Statement): Seq[(String, String)] = s match {
    case b: Block => b.stmts flatMap {s: Statement => grabMemInfo(s)}
    case c: Connect => {
      firrtl.Utils.kind(c.loc) match {
        case firrtl.MemKind => Seq((emitExpr(c.loc), emitExpr(c.expr)))
        case _ => Seq()
      }
    }
    case _ => Seq()
  }

  def grabMemAddr(str: String): String = {
    if (str.contains('[')) str.slice(str.indexOf('[')+1, str.lastIndexOf(']'))
    else str
  }

  def memHasRightParams(m: DefMemory) = {
    (m.writeLatency == 1) && (m.readLatency == 0) && (m.readwriters.isEmpty)
  }


  // State initialization methods
  def makeRegisterUpdate(prefix: String)(r: DefRegister): String = {
    val regName = prefix + r.name
    val resetName = emitExpr(r.reset)
    val resetVal = r.init match {
      case l: Literal => emitExpr(r.init)
      case _ => if (resetName != "0x0")
        throw new Exception("register reset isn't a literal " + r.init)
    }
    if (resetName == "0x0") s"$regName = $regName$$next;"
    else s"$regName = $resetName ? $resetVal : $regName$$next;"
  }

  def initializeVals(topLevel: Boolean)(m: Module, registers: Seq[DefRegister], memories: Seq[DefMemory]) = {
    def initVal(name: String, tpe:Type) = {
      val width = bitWidth(tpe).toInt
      if (width > 64)
        s"""$name = mpz_class("${BigInt(width,Random).toString(16)}",16);"""
      else if (width > 32) s"$name = rand();"
      else tpe match {
        case UIntType(_) => s"$name = rand() & ${genMask(tpe)};"
        case SIntType(_) => {
          val shamt = 32 - width
          s"$name = (rand() << $shamt) >> $shamt;"
        }
      }
    }
    val regInits = registers map {
      r: DefRegister => initVal(r.name + "$next", r.tpe)
    }
    val memInits = memories map { m: DefMemory => {
      s"for (size_t a=0; a < ${m.depth}; a++) ${m.name}[a] = rand() & ${genMask(m.dataType)};"
    }}
    val portInits = m.ports flatMap { p => p.tpe match {
      case ClockType => Seq()
      case _ => if ((p.name != "reset") && !topLevel) Seq()
                else Seq(initVal(p.name, p.tpe))
    }}
    regInits ++ memInits ++ portInits
  }


  // Emission methods
  def emitPort(topLevel: Boolean)(p: Port): Seq[String] = p.tpe match {
    case ClockType => Seq()
    case _ => if ((p.name != "reset") && !topLevel) Seq()
              else Seq(genCppType(p.tpe) + " " + p.name + ";")
  }

  def emitExpr(e: Expression): String = e match {
    case w: WRef => w.name
    case u: UIntLiteral => {
      if (bitWidth(u.tpe) > 64) s"""mpz_class("${u.value.toString(10)}",10)"""
      else "0x" + u.value.toString(16)
    }
    case u: SIntLiteral => {
      if (bitWidth(u.tpe) > 64) s"""mpz_class("${u.value.toString(10)}",10)"""
      else u.value.toString(10)
    }
    case m: Mux => {
      val condName = emitExpr(m.cond)
      val tvalName = emitExpr(m.tval)
      val fvalName = emitExpr(m.fval)
      s"$condName ? $tvalName : $fvalName"
    }
    case w: WSubField => s"${emitExpr(w.exp)}.${w.name}"
    case p: DoPrim => p.op match {
      case Add => p.args map emitExpr mkString(" + ")
      case Addw => p.args map emitExpr mkString(" + ")
      case Sub => p.args map emitExpr mkString(" - ")
      case Subw => p.args map emitExpr mkString(" - ")
      case Mul => {
        val argNames = p.args map emitExpr
        val possiblyCast =
          // assuming args are already same width
          if ((bitWidth(p.tpe) > 64) && (bitWidth(p.args.head.tpe) <= 64))
            argNames map {name => s"fromUInt($name)"}
          else argNames
        possiblyCast mkString(" * ")
      }
      case Div => p.args map emitExpr mkString(" / ")
      case Rem => p.args map emitExpr mkString(" % ")
      case Lt  => p.args map emitExpr mkString(" < ")
      case Leq => p.args map emitExpr mkString(" <= ")
      case Gt  => p.args map emitExpr mkString(" > ")
      case Geq => p.args map emitExpr mkString(" >= ")
      case Eq => p.args map emitExpr mkString(" == ")
      case Neq => p.args map emitExpr mkString(" != ")
      case Pad => {
        if ((bitWidth(p.tpe) > 64) && (bitWidth(p.args.head.tpe) <= 64))
          s"fromUInt(${emitExpr(p.args.head)})"
        else emitExpr(p.args.head)
      }
      case AsUInt => {
        if (bitWidth(p.tpe) > 64) emitExpr(p.args.head)
        else p.args.head.tpe match {
          case UIntType(_) => emitExpr(p.args.head)
          case SIntType(_) => s"static_cast<uint64_t>(${emitExpr(p.args.head)}) & ${genMask(p.tpe)}"
        }
      }
      case AsSInt => {
        if (bitWidth(p.tpe) > 64) emitExpr(p.args.head)
        else p.args.head.tpe match {
          case UIntType(_) => {
            val shamt = 64 - bitWidth(p.args.head.tpe)
            s"((static_cast<int64_t>(${emitExpr(p.args.head)}))<<$shamt)>>$shamt"
          }
          case SIntType(_) => emitExpr(p.args.head)
        }
      }
      case AsClock => throw new Exception("AsClock unimplemented!")
      case Shl => s"${emitExpr(p.args.head)} << ${p.consts.head.toInt}"
      case Shlw => s"${emitExpr(p.args.head)} << ${p.consts.head.toInt}"
      case Shr => if ((bitWidth(p.tpe) <= 64) && (bitWidth(p.args(0).tpe) > 64))
            s"mpz_class(${emitExpr(p.args.head)} >> ${p.consts.head.toInt}).get_ui()"
          else
            s"${emitExpr(p.args.head)} >> ${p.consts.head.toInt}"
      case Dshl => p.args map emitExpr mkString(" << ")
      case Dshlw => p.args map emitExpr mkString(" << ")
      case Dshr => p.args map emitExpr mkString(" >> ")
      case Cvt => {
        if (bitWidth(p.tpe) > 63) {
          if (bitWidth(p.args.head.tpe) == 64) s"fromUInt(${emitExpr(p.args.head)})"
          else emitExpr(p.args.head)
        } else p.args.head.tpe match {
          case UIntType(_) => s"static_cast<int64_t>(${emitExpr(p.args.head)})"
          case SIntType(_) => emitExpr(p.args.head)
        }
      }
      case Neg => s"-${emitExpr(p.args.head)}"
      case Not => {
        if (bitWidth(p.tpe) > 64) s"~${emitExpr(p.args.head)}"
        else s"(~${emitExpr(p.args.head)}) & ${genMask(p.tpe)}"
      }
      case And => p.args map emitExpr mkString(" & ")
      case Or => p.args map emitExpr mkString(" | ")
      case Xor => p.args map emitExpr mkString(" ^ ")
      case Andr => throw new Exception("Andr unimplemented!")
      case Orr => throw new Exception("Orr unimplemented!")
      case Xorr => throw new Exception("Xorr unimplemented!")
      case Cat => {
        val shamt = bitWidth(p.args(1).tpe)
        if (bitWidth(p.tpe) > 64) {
          val upper = if (bitWidth(p.args(0).tpe) > 64) emitExpr(p.args(0))
                      else s"fromUInt(${emitExpr(p.args(0))})"
          val lower = if (bitWidth(p.args(1).tpe) > 64) emitExpr(p.args(1))
                      else s"fromUInt(${emitExpr(p.args(1))})"
          s"($upper << $shamt) | $lower"
        } else {
          val needL = p.args(0) match {
            case u: UIntLiteral => "l"
            case _ => ""
          }
          s"(${emitExpr(p.args(0))}$needL << $shamt) | ${emitExpr(p.args(1))}"
        }
      }
      case Bits => {
        val name = emitExpr(p.args.head)
        if (bitWidth(p.args.head.tpe) > 64) {
          val internalShift = if (p.consts(1) == 0) name
            else s"($name >> ${p.consts(1)})"
          if (bitWidth(p.tpe) > 64) s"$internalShift & ${genMask(p.tpe)}"
          else s"mpz_class($internalShift).get_ui() & ${genMask(p.tpe)}"
        } else {
          val hi_shamt = 64 - p.consts(0).toInt - 1
          val lo_shamt = p.consts(1).toInt + hi_shamt
          s"($name << $hi_shamt) >> $lo_shamt"
        }
      }
      case Head => {
        val shamt = bitWidth(p.args.head.tpe) - p.consts.head.toInt
        s"${emitExpr(p.args.head)} >> shamt"
      }
      case Tail => s"${emitExpr(p.args.head)} & ${genMask(p.tpe)}"
    }
    case _ => throw new Exception(s"Don't yet support $e")
  }

  def emitStmt(s: Statement): Seq[String] = s match {
    case b: Block => b.stmts flatMap {s: Statement => emitStmt(s)}
    case d: DefNode => {
      val lhs = if (bitWidth(d.value.tpe) > 64) d.name
                else genCppType(d.value.tpe) + " " + d.name
      val rhs = emitExpr(d.value)
      Seq(s"$lhs = $rhs;")
    }
    case c: Connect => {
      val lhs = emitExpr(c.loc)
      val rhs = emitExpr(c.expr)
      firrtl.Utils.kind(c.loc) match {
        case firrtl.MemKind => Seq()
        case firrtl.RegKind => Seq(s"$lhs$$next = $rhs;")
        case firrtl.WireKind => {
          if (bitWidth(c.loc.tpe) > 64) Seq(s"$lhs = $rhs;")
          else Seq(s"${genCppType(c.loc.tpe)} $lhs = $rhs;")
        }
        case firrtl.PortKind => {
          if (lhs.contains("$")) {
            if (bitWidth(c.loc.tpe) > 64) Seq(s"$lhs = $rhs;")
            else Seq(s"${genCppType(c.loc.tpe)} $lhs = $rhs;")
          } else Seq(s"$lhs = $rhs;")
        }
        case firrtl.InstanceKind => {
          if (lhs.contains(".")) Seq(s"$lhs = $rhs;")
          else {
            if (bitWidth(c.loc.tpe) > 64) Seq(s"$lhs = $rhs;")
            else Seq(s"${genCppType(c.loc.tpe)} $lhs = $rhs;")
          }
        }
        case _ => Seq(s"$lhs = $rhs;")
      }
    }
    case p: Print => {
      val formatters = "(%h)|(%d)|(%ld)".r.findAllIn(p.string.serialize).toList
      val argWidths = p.args map {e: Expression => bitWidth(e.tpe)}
      val replacements = formatters zip argWidths map { case(format, width) =>
        if (format == "%h") {
          val printWidth = math.ceil((width/4).toDouble).toInt
          (format, s"%0${printWidth}llx")
        } else {
          val printWidth = math.ceil(math.log10((1l<<width.toInt).toDouble)).toInt
          (format, s"%${printWidth}llu")
        }
      }
      val formatString = replacements.foldLeft(p.string.serialize){
        case (str, (searchFor, replaceWith)) => str.replaceFirst(searchFor, replaceWith)
      }
      val printfArgs = Seq(s""""$formatString"""") ++ (p.args map emitExpr)
      Seq(s"if (${emitExpr(p.en)}) printf(${printfArgs mkString(", ")});")
    }
    case st: Stop => Seq(s"if (${emitExpr(st.en)}) exit(${st.ret});")
    case r: DefRegister => Seq()
    case w: DefWire => Seq()
    case m: DefMemory => Seq()
    case i: WDefInstance => Seq()
    case _ => throw new Exception(s"Don't yet support $s")
  }

  def emitBody(m: Module, circuit: Circuit, prefix: String) = {
    val body = addPrefixToNameStmt(prefix)(m.body)
    val registers = findRegisters(body)
    val memories = findMemory(body)
    memories foreach {m =>
      if(!memHasRightParams(m)) throw new Exception(s"improper mem! $m")}
    val regUpdates = registers map makeRegisterUpdate(prefix)
    val nodeNames = findNodes(body) map { _.name }
    val wireNames = findWires(body) map { prefix + _.name }
    // FUTURE: remove unneeded or identity renames
    val externalPortNames = findPortNames(m) map { prefix + _ }
    val internalPortNames = findModuleInstances(m.body) flatMap {
      case (moduleType, moduleName) =>
        findPortNames(findModule(moduleType, circuit)) map {prefix + s"$moduleName." + _}
    }
    val allTempSigs = nodeNames ++ wireNames ++ externalPortNames ++ internalPortNames
    val renames = (allTempSigs map { s: String =>
      (s, if (s.contains(".")) s.replace('.','$') else s)
    }).toMap
    val memConnects = grabMemInfo(body).toMap
    val memWriteCommands = memories flatMap {m: DefMemory => {
      m.writers map { writePortName:String => {
        val wrEnName = memConnects(s"$prefix${m.name}.$writePortName.en")
        val wrAddrName = memConnects(s"$prefix${m.name}.$writePortName.addr")
        val wrDataName = memConnects(s"$prefix${m.name}.$writePortName.data")
        val wrMaskName = memConnects(s"$prefix${m.name}.$writePortName.mask")
        val wrEnNameRep = renames.getOrElse(wrEnName, wrEnName)
        val wrAddrNameRep = renames.getOrElse(wrAddrName, wrAddrName)
        val wrDataNameRep = renames.getOrElse(wrDataName, wrDataName)
        val wrMaskNameRep = renames.getOrElse(wrMaskName, wrMaskName)
        s"if ($wrEnNameRep && $wrMaskNameRep) $prefix${m.name}[$wrAddrNameRep] = $wrDataNameRep;"
      }}
    }}
    val readOutputs = memories flatMap {m: DefMemory => {
      m.readers map { readPortName:String =>
        val rdAddrName = memConnects(s"$prefix${m.name}.$readPortName.addr")
        val rdDataName = s"$prefix${m.name}.$readPortName.data"
        val rdAddrRep = renames.getOrElse(rdAddrName, rdAddrName)
        val rdDataRep = renames.getOrElse(rdDataName, rdDataName)
        (rdDataRep, s"$prefix${m.name}[$rdAddrRep]")
      }
    }}
    val readMappings = readOutputs.toMap
    val namesReplaced = replaceNamesStmt(readMappings ++ renames)(body)
    (regUpdates, namesReplaced, memWriteCommands)
  }

  def emitPrintsAndStops(stopAndPrints: Seq[Statement]): Seq[String] = {
    val (prints, stops) = stopAndPrints partition { _ match {
      case p: Print => true
      case _ => false
    }}
    Seq("if (done_reset && update_registers) {") ++ Seq("if(verbose) {") ++
      (prints flatMap emitStmt) ++ Seq("}") ++ (stops flatMap emitStmt) ++ Seq("}")
  }
}
