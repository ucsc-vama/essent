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

  // Type Declaration & Initialization
  //----------------------------------------------------------------------------
  def genCppType(tpe: Type) = tpe match {
    case UIntType(IntWidth(w)) => s"UInt<$w>"
    case SIntType(IntWidth(w)) => s"SInt<$w>"
    case AsyncResetType => "UInt<1>"
    case _ => throw new Exception(s"No CPP type implemented for $tpe")
  }

  def initializeVals(topLevel: Boolean)(m: Module, registers: Seq[DefRegister], memories: Seq[DefMemory]) = {
    def initVal(name: String, tpe:Type) = s"$name.rand_init();"
    val regInits = registers map {
      r: DefRegister => initVal(r.name, r.tpe)
    }
    val memInits = memories flatMap { m: DefMemory => {
      if ((m.depth > 1000) && (bitWidth(m.dataType)) <= 64) {
        Seq(s"${m.name}[0].rand_init();",
            s"for (size_t a=0; a < ${m.depth}; a++) ${m.name}[a] = ${m.name}[0].as_single_word() + a;")
      } else
        Seq(s"for (size_t a=0; a < ${m.depth}; a++) ${m.name}[a].rand_init();")
    }}
    val portInits = m.ports flatMap { p => p.tpe match {
      case ClockType => Seq()
      case _ => if (!topLevel) Seq()
                else Seq(initVal(p.name, p.tpe))
    }}
    regInits ++ memInits ++ portInits
  }


  // Prefixing & Replacement
  //----------------------------------------------------------------------------
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

  def replaceNamesStmt(renames: Map[String, String])(s: Statement): Statement = {
    val nodeReplaced = s match {
      case n: DefNode if (renames.contains(n.name)) => n.copy(name = renames(n.name))
      case cm: CondMux if (renames.contains(cm.name)) => cm.copy(name = renames(cm.name))
      case mw: MemWrite if (renames.contains(mw.memName)) => mw.copy(memName = renames(mw.memName))
      case _ => s
    }
    nodeReplaced map replaceNamesStmt(renames) map replaceNamesExpr(renames)
  }

  def replaceNamesExpr(renames: Map[String, String])(e: Expression): Expression = {
    def findRootKind(e: Expression): Kind = e match {
      case w: WRef => w.kind
      case w: WSubField => findRootKind(w.expr)
    }
    e match {
      case w: WRef => {
        if (renames.contains(w.name)) w.copy(name = renames(w.name))
        else w
      }
      case w: WSubField => {
        val fullName = emitExpr(w)
        // flattens out nested WSubFields
        if (renames.contains(fullName)) WRef(renames(fullName), w.tpe, findRootKind(w), w.flow)
        else w
      }
      case _ => e map replaceNamesExpr(renames)
    }
  }


  // Emission
  //----------------------------------------------------------------------------
  def emitPort(topLevel: Boolean)(p: Port): Seq[String] = p.tpe match {
    case ClockType => if (!topLevel) Seq()
                      else Seq(genCppType(UIntType(IntWidth(1))) + " " + p.name + ";")
      // FUTURE: suppress generation of clock field if not making harness (or used)?
    case _ => if (!topLevel) Seq()
              else Seq(genCppType(p.tpe) + " " + p.name + ";")
  }

  def chunkLitString(litStr: String, chunkWidth:Int = 16): Seq[String] = {
    if (litStr.length % chunkWidth == 0) litStr.grouped(chunkWidth).toSeq
    else Seq(litStr.take(litStr.length % chunkWidth)) ++ chunkLitString(litStr.drop(litStr.length % chunkWidth), chunkWidth)
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

  def emitExpr(e: Expression)(implicit rn: Renamer = null): String = e match {
    case w: WRef => if (rn != null) rn.emit(w.name) else w.name
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
      val condName = emitExprWrap(m.cond)
      val tvalName = emitExprWrap(m.tval)
      val fvalName = emitExprWrap(m.fval)
      s"$condName ? $tvalName : $fvalName"
    }
    case w: WSubField => {
      val result = s"${emitExpr(w.expr)(null)}.${w.name}"
      if (rn != null)
        rn.emit(result)
      else
        result
    }
    case w: WSubAccess => s"${emitExpr(w.expr)}[${emitExprWrap(w.index)}.as_single_word()]"
    case p: DoPrim => p.op match {
      case Add => p.args map emitExprWrap mkString(" + ")
      case Addw => s"${emitExprWrap(p.args(0))}.addw(${emitExprWrap(p.args(1))})"
      case Sub => p.args map emitExprWrap mkString(" - ")
      case Subw => s"${emitExprWrap(p.args(0))}.subw(${emitExprWrap(p.args(1))})"
      case Mul => p.args map emitExprWrap mkString(" * ")
      case Div => p.args map emitExprWrap mkString(" / ")
      case Rem => p.args map emitExprWrap mkString(" % ")
      case Lt  => p.args map emitExprWrap mkString(" < ")
      case Leq => p.args map emitExprWrap mkString(" <= ")
      case Gt  => p.args map emitExprWrap mkString(" > ")
      case Geq => p.args map emitExprWrap mkString(" >= ")
      case Eq => p.args map emitExprWrap mkString(" == ")
      case Neq => p.args map emitExprWrap mkString(" != ")
      case Pad => s"${emitExprWrap(p.args.head)}.pad<${bitWidth(p.tpe)}>()"
      case AsUInt => s"${emitExprWrap(p.args.head)}.asUInt()"
      case AsSInt => s"${emitExprWrap(p.args.head)}.asSInt()"
      case AsClock => throw new Exception("AsClock unimplemented!")
      case AsAsyncReset => emitExpr(p.args.head) // TODO: make async
      case Shl => s"${emitExprWrap(p.args.head)}.shl<${p.consts.head.toInt}>()"
      // case Shlw => s"${emitExprWrap(p.args.head)}.shlw<${p.consts.head.toInt}>()"
      case Shr => s"${emitExprWrap(p.args.head)}.shr<${p.consts.head.toInt}>()"
      case Dshl => p.args map emitExprWrap mkString(" << ")
      case Dshlw => s"${emitExprWrap(p.args(0))}.dshlw(${emitExpr(p.args(1))})"
      case Dshr => p.args map emitExprWrap mkString(" >> ")
      case Cvt => s"${emitExprWrap(p.args.head)}.cvt()"
      case Neg => s"-${emitExprWrap(p.args.head)}"
      case Not => s"~${emitExprWrap(p.args.head)}"
      case And => p.args map emitExprWrap mkString(" & ")
      case Or => p.args map emitExprWrap mkString(" | ")
      case Xor => p.args map emitExprWrap mkString(" ^ ")
      case Andr => s"${emitExprWrap(p.args.head)}.andr()"
      case Orr => s"${emitExprWrap(p.args.head)}.orr()"
      case Xorr => s"${emitExprWrap(p.args.head)}.xorr()"
      case Cat => s"${emitExprWrap(p.args(0))}.cat(${emitExpr(p.args(1))})"
      case Bits => s"${emitExprWrap(p.args.head)}.bits<${p.consts(0).toInt},${p.consts(1).toInt}>()"
      case Head => s"${emitExprWrap(p.args.head)}.head<${p.consts.head.toInt}>()"
      case Tail => s"${emitExprWrap(p.args.head)}.tail<${p.consts.head.toInt}>()"
    }
    case _ => throw new Exception(s"Don't yet support $e")
  }

  def emitExprWrap(e: Expression)(implicit rn: Renamer): String = e match {
    case DoPrim(_,_,_,_) | Mux(_,_,_,_) => s"(${emitExpr(e)})"
    case _ => emitExpr(e)
  }

  def emitStmt(s: Statement)(implicit rn: Renamer): Seq[String] = s match {
    case b: Block => b.stmts flatMap emitStmt
    case d: DefNode => {
      val lhs_orig = d.name
      val lhs = rn.emit(lhs_orig)
      val rhs = emitExpr(d.value)
      if (rn.decLocal(lhs_orig)) Seq(s"${genCppType(d.value.tpe)} $lhs = $rhs;")
      else Seq(s"$lhs = $rhs;")
    }
    case c: Connect => {
      val lhs_orig = emitExpr(c.loc)(null)
      val lhs = rn.emit(lhs_orig)
      val rhs = emitExpr(c.expr)
      if (rn.decLocal(lhs_orig)) Seq(s"${genCppType(c.loc.tpe)} $lhs = $rhs;")
      else Seq(s"$lhs = $rhs;")
    }
    case p: Print => {
      val formatters = "(%h)|(%x)|(%d)|(%ld)".r.findAllIn(p.string.serialize).toList
      val argWidths = p.args map {e: Expression => bitWidth(e.tpe)}
      if (!(argWidths forall { _ <= 64 })) throw new Exception(s"Can't print wide signals")
      val replacements = formatters zip argWidths map { case(format, width) =>
        if (format == "%h" || format == "%x") {
          val printWidth = math.ceil(width.toDouble/4).toInt
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
                        (p.args map {arg => s"${emitExprWrap(arg)}.as_single_word()"})
      Seq(s"if (UNLIKELY(done_reset && update_registers && verbose && ${emitExprWrap(p.en)})) printf(${printfArgs mkString(", ")});")
    }
    case st: Stop => {
      Seq(s"if (UNLIKELY(${emitExpr(st.en)})) {assert_triggered = true; assert_exit_code = ${st.ret};}")
    }
    case mw: MemWrite => {
      Seq(s"if (UNLIKELY(update_registers && ${emitExprWrap(mw.wrEn)} && ${emitExprWrap(mw.wrMask)})) ${mw.memName}[${emitExprWrap(mw.wrAddr)}.as_single_word()] = ${emitExpr(mw.wrData)};")
    }
    case ru: RegUpdate => Seq(s"if (update_registers) ${emitExpr(ru.regRef)} = ${emitExpr(ru.expr)};")
    case r: DefRegister => Seq()
    case w: DefWire => Seq()
    case m: DefMemory => Seq()
    case i: WDefInstance => Seq()
    case _ => throw new Exception(s"Don't yet support $s")
  }
}
