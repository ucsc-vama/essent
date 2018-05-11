package essent

import essent.Extract._
import essent.ir._

import firrtl._
import firrtl.annotations._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.PrimOps._
import firrtl.Utils._

import scala.util.Random

object Emitter {
  case class HyperedgeDep(name: String, deps: Seq[String], stmt: Statement)

  // Declaration Methods
  def genCppType(tpe: Type) = tpe match {
    case UIntType(IntWidth(w)) => s"UInt<$w>"
    case SIntType(IntWidth(w)) => s"SInt<$w>"
    case _ => throw new Exception(s"No CPP type implemented for $tpe")
  }


  // Replacement methods
  def addPrefixToNameStmt(prefix: String)(s: Statement): Statement = {
    val replaced = s match {
      case n: DefNode => n.copy(name = prefix + n.name)
      case r: DefRegister => r.copy(name = prefix + r.name)
      case m: DefMemory => m.copy(name = prefix + m.name)
      case w: DefWire => w.copy(name = prefix + w.name)
      case mw: MemWrite => mw.copy(memName = prefix + mw.memName)
      case _ => s
    }
    replaced map addPrefixToNameStmt(prefix) map addPrefixToNameExpr(prefix)
  }

  def addPrefixToNameExpr(prefix: String)(e: Expression): Expression = {
    val replaced = e match {
      case w: WRef => w.copy(name = prefix + w.name)
      case _ => e
    }
    replaced map addPrefixToNameExpr(prefix)
  }

  def findRootKind(e: Expression): Kind = e match {
    case w: WRef => w.kind
    case w: WSubField => findRootKind(w.expr)
  }

  def replaceNamesStmt(renames: Map[String, String])(s: Statement): Statement = {
    val nodeReplaced = s match {
      case n: DefNode => {
        if (renames.contains(n.name)) n.copy(name = renames(n.name))
        else n
      }
      case ms: MuxShadowed => {
        if (renames.contains(ms.name)) ms.copy(name = renames(ms.name))
        else ms
      }
      case mw: MemWrite => {
        if (renames.contains(mw.memName)) mw.copy(memName = renames(mw.memName))
        else mw
      }
      case _ => s
    }
    nodeReplaced map replaceNamesStmt(renames) map replaceNamesExpr(renames)
  }

  def replaceNamesExpr(renames: Map[String, String])(e: Expression): Expression = e match {
    case w: WRef => {
      if (renames.contains(w.name)) w.copy(name = renames(w.name))
      else w
    }
    case w: WSubField => {
      val fullName = emitExpr(w)
      // flattens out nested WSubFields
      if (renames.contains(fullName)) WRef(renames(fullName), w.tpe, findRootKind(w), w.gender)
      else w
    }
    case _ => e map replaceNamesExpr(renames)
  }


  // State initialization methods
  def makeRegisterUpdate(prefix: String)(r: DefRegister): String = {
    val regName = prefix + r.name
    val resetName = emitExpr(r.reset)
    val resetVal = r.init match {
      case l: Literal => emitExpr(r.init)
      case _ => if (resetName != "UInt<1>(0x0)")
        throw new Exception("register reset isn't a literal " + r.init)
    }
    if (resetName == "UInt<1>(0x0)") s"$regName = $regName$$next;"
    else s"$regName = $resetName ? $resetVal : $regName$$next;"
  }

  def initializeVals(topLevel: Boolean)(m: Module, registers: Seq[DefRegister], memories: Seq[DefMemory]) = {
    def initVal(name: String, tpe:Type) = s"$name.rand_init();"
    val regInits = registers map {
      r: DefRegister => initVal(r.name, r.tpe)
    }
    val memInits = memories map { m: DefMemory => {
      s"for (size_t a=0; a < ${m.depth}; a++) ${m.name}[a].rand_init();"
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

  def emitRegUpdate(r: DefRegister): String = {
    val regName = r.name
    val resetName = emitExpr(r.reset)
    if (resetName == "UInt<1>(0x0)") s"$regName = $regName$$next;"
    else {
      val resetVal = r.init match {
        case l: Literal => emitExpr(r.init)
        case _ => throw new Exception("register reset isn't a literal " + r.init)
      }
      s"$regName = $resetName ? $resetVal : $regName$$next;"
    }
  }

  def chunkLitString(litStr: String, chunkWidth:Int = 16): Seq[String] = {
    if (litStr.size < chunkWidth) Seq(litStr)
    else chunkLitString(litStr.dropRight(chunkWidth)) ++ Seq(litStr.takeRight(chunkWidth))
  }

  // NOTE: assuming no large UIntLiteral is negative
  def splatLargeLiteralIntoRawArray(value: BigInt, width: BigInt): String = {
    val rawHexStr = value.toString(16)
    val isNeg = value < 0
    val asHexStr = if (isNeg) rawHexStr.tail else rawHexStr
    val arrStr = chunkLitString(asHexStr) map { "0x" + _} mkString(",")
    val leadingNegStr = if (isNeg) "(uint64_t) -" else ""
    val numWords = (width + 63) / 64
    s"std::array<uint64_t,$numWords>({$leadingNegStr$arrStr})"
  }

  def emitExpr(e: Expression): String = e match {
    case w: WRef => w.name
    case u: UIntLiteral => {
      val maxIn64Bits = (BigInt(1) << 64) - 1
      val width = bitWidth(u.tpe)
      val asHexStr = u.value.toString(16)
      if ((width <= 64) || (u.value <= maxIn64Bits)) s"UInt<$width>(0x$asHexStr)"
      else s"UInt<$width>(${splatLargeLiteralIntoRawArray(u.value, width)})"
    }
    case u: SIntLiteral => {
      val width = bitWidth(u.tpe)
      if (width <= 64) s"SInt<$width>(${u.value.toString(10)})"
      else s"SInt<$width>(${splatLargeLiteralIntoRawArray(u.value, width)})"
    }
    case m: Mux => {
      val condName = emitExpr(m.cond)
      val tvalName = emitExpr(m.tval)
      val fvalName = emitExpr(m.fval)
      s"$condName ? $tvalName : $fvalName"
    }
    case w: WSubField => s"${emitExpr(w.expr)}.${w.name}"
    case w: WSubAccess => s"${emitExpr(w.expr)}[${emitExpr(w.index)}.as_single_word()]"
    case p: DoPrim => p.op match {
      case Add => p.args map emitExpr mkString(" + ")
      case Addw => s"${emitExpr(p.args(0))}.addw(${emitExpr(p.args(1))})"
      case Sub => p.args map emitExpr mkString(" - ")
      case Subw => s"${emitExpr(p.args(0))}.subw(${emitExpr(p.args(1))})"
      case Mul => p.args map emitExpr mkString(" * ")
      case Div => p.args map emitExpr mkString(" / ")
      case Rem => p.args map emitExpr mkString(" % ")
      case Lt  => p.args map emitExpr mkString(" < ")
      case Leq => p.args map emitExpr mkString(" <= ")
      case Gt  => p.args map emitExpr mkString(" > ")
      case Geq => p.args map emitExpr mkString(" >= ")
      case Eq => p.args map emitExpr mkString(" == ")
      case Neq => p.args map emitExpr mkString(" != ")
      case Pad => s"${emitExpr(p.args.head)}.pad<${bitWidth(p.tpe)}>()"
      case AsUInt => s"${emitExpr(p.args.head)}.asUInt()"
      case AsSInt => s"${emitExpr(p.args.head)}.asSInt()"
      case AsClock => throw new Exception("AsClock unimplemented!")
      case Shl => s"${emitExpr(p.args.head)}.shl<${p.consts.head.toInt}>()"
      case Shlw => s"${emitExpr(p.args.head)}.shlw<${p.consts.head.toInt}>()"
      case Shr => s"${emitExpr(p.args.head)}.shr<${p.consts.head.toInt}>()"
      case Dshl => p.args map emitExpr mkString(" << ")
      case Dshlw => s"${emitExpr(p.args(0))}.dshlw(${emitExpr(p.args(1))})"
      case Dshr => p.args map emitExpr mkString(" >> ")
      case Cvt => s"${emitExpr(p.args.head)}.cvt()"
      case Neg => s"-${emitExpr(p.args.head)}"
      case Not => s"~${emitExpr(p.args.head)}"
      case And => p.args map emitExpr mkString(" & ")
      case Or => p.args map emitExpr mkString(" | ")
      case Xor => p.args map emitExpr mkString(" ^ ")
      case Andr => throw new Exception("Andr unimplemented!")
      case Orr => throw new Exception("Orr unimplemented!")
      case Xorr => throw new Exception("Xorr unimplemented!")
      case Cat => s"${emitExpr(p.args(0))}.cat(${emitExpr(p.args(1))})"
      case Bits => s"${emitExpr(p.args.head)}.bits<${p.consts(0).toInt},${p.consts(1).toInt}>()"
      case Head => s"${emitExpr(p.args.head)}.head<${p.consts.head.toInt}>()"
      case Tail => s"(${emitExpr(p.args.head)}).tail<${p.consts.head.toInt}>()"
    }
    case _ => throw new Exception(s"Don't yet support $e")
  }

  def emitStmt(doNotDec: Set[String])(s: Statement): Seq[String] = s match {
    case b: Block => b.stmts flatMap {s: Statement => emitStmt(doNotDec)(s)}
    case d: DefNode => {
      val lhs = d.name
      val rhs = emitExpr(d.value)
      if (doNotDec.contains(lhs)) Seq(s"$lhs = $rhs;")
      else Seq(s"${genCppType(d.value.tpe)} $lhs = $rhs;")
    }
    case c: Connect => {
      val lhs = emitExpr(c.loc)
      val rhs = emitExpr(c.expr)
      if (doNotDec.contains(lhs)) Seq(s"$lhs = $rhs;")
      else Seq(s"${genCppType(c.loc.tpe)} $lhs = $rhs;")
    }
    case p: Print => {
      val formatters = "(%h)|(%d)|(%ld)".r.findAllIn(p.string.serialize).toList
      val argWidths = p.args map {e: Expression => bitWidth(e.tpe)}
      if (!(argWidths forall { _ <= 64 })) throw new Exception(s"Can't print wide signals")
      val replacements = formatters zip argWidths map { case(format, width) =>
        if (format == "%h") {
          val printWidth = math.ceil((width/4).toDouble).toInt
          (format, s"""%0${printWidth}" PRIx64 """")
        } else {
          val printWidth = math.ceil(math.log10((1l<<width.toInt).toDouble)).toInt
          (format, s"""%${printWidth}" PRIu64 """")
        }
      }
      val formatString = replacements.foldLeft(p.string.serialize){
        case (str, (searchFor, replaceWith)) => str.replaceFirst(searchFor, replaceWith)
      }
      val printfArgs = Seq(s""""$formatString"""") ++
                        (p.args map {arg => s"${emitExpr(arg)}.as_single_word()"})
      Seq(s"if (done_reset && update_registers && verbose && ${emitExpr(p.en)}) printf(${printfArgs mkString(", ")});")
    }
    case st: Stop => {
      Seq(s"if (${emitExpr(st.en)}) {assert_triggered = true; assert_exit_code = ${st.ret};}")
    }
    case mw: MemWrite => {
      Seq(s"if (update_registers && ${emitExpr(mw.wrEn)} && ${emitExpr(mw.wrMask)}) ${mw.memName}[${emitExpr(mw.wrAddr)}.as_single_word()] = ${emitExpr(mw.wrData)};")
    }
    case ru: RegUpdate => Seq(s"if (update_registers) ${emitExpr(ru.regRef)} = ${emitExpr(ru.expr)};")
    case r: DefRegister => Seq()
    case w: DefWire => Seq()
    case m: DefMemory => Seq()
    case i: WDefInstance => Seq()
    case _ => throw new Exception(s"Don't yet support $s")
  }

  def flattenBodies(m: Module, circuit: Circuit, prefix: String) = {
    val body = addPrefixToNameStmt(prefix)(m.body)
    val nodeNames = findNodes(body) map { _.name }
    val wireNames = findWires(body) map { _.name }
    val externalPortNames = findPortNames(m) map { prefix + _ }
    val internalPortNames = findModuleInstances(m.body) flatMap {
      case (moduleType, moduleName) =>
        findPortNames(findModule(moduleType, circuit)) map {prefix + s"$moduleName." + _}
    }
    val allTempSigs = nodeNames ++ wireNames ++ externalPortNames ++ internalPortNames
    val renames = (allTempSigs filter { _.contains('.') } map { s => (s, s.replace('.','$'))}).toMap
    replaceNamesStmt(renames)(body)
  }
}
