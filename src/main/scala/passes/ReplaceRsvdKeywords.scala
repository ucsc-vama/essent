package essent.passes

import firrtl.{DependencyAPIMigration, Transform, WRef}
import firrtl.ir._
import firrtl.passes.Pass

object ReplaceRsvdKeywords extends Pass {
  val reservedWords = Set("asm" ,	"else",	"new",	"this",
    "auto",	"enum",	"operator",	"throw",
    "bool",	"explicit",	"private",	"true",
    "break",	"export",	"protected",	"try",
    "case",	"extern",	"public",	"typedef",
    "catch",	"false",	"register",	"typeid",
    "char",	"float",	"reinterpret_cast",	"typename",
    "class",	"for",	"return",	"union",
    "const",	"friend",	"short",	"unsigned",
    "const_cast",	"goto",	"signed",	"using",
    "continue",	"if",	"sizeof",	"virtual",
    "default",	"inline",	"static",	"void",
    "delete",	"int",	"static_cast",	"volatile",
    "do",	"long",	"struct",	"wchar_t",
    "double",	"mutable",	"switch",	"while",
    "dynamic_cast",	"namespace",	"template",
    "And",	"bitor",	"not_eq",	"xor",
    "and_eq",	"compl",	"or",	"xor_eq",
    "bitand",	"not",	"or_eq", "UNLIKELY",
    "PARTflags", "update_registers","verbose",
    "done_reset" , "sim_cached","regs_set",
    "assert_triggered","assert_exit_code")

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false
  private def renameWord(oldName: String): String = oldName + "$"
  private def maybeRename(oldName: String): String =
    if (reservedWords.contains(oldName)) renameWord(oldName)
    else oldName

  private def analyzeExpression(e: Expression): Expression = e match {
    case r: Reference => r.copy(name = maybeRename(r.name))
    case m: Mux => m.mapExpr(analyzeExpression)
    case s: SubField => s.copy(name = maybeRename(s.name)).mapExpr(analyzeExpression)
    case d: DoPrim => d.mapExpr(analyzeExpression)
    case si: SubIndex => si.mapExpr(analyzeExpression)
    case sa: SubAccess => sa.mapExpr(analyzeExpression)
    case vi: ValidIf => vi.mapExpr(analyzeExpression)
    case _ => e
  }

  private def analyzeStatement(s: Statement): Statement = s match {
    case d: DefNode => d.copy(name = maybeRename(d.name)).mapExpr(analyzeExpression)
    case c: Connect => c.mapExpr(analyzeExpression)
    case pc: PartialConnect => pc.mapExpr(analyzeExpression)
    case b: Block => b.mapStmt(analyzeStatement)
    case dw: DefWire => dw.copy(name = maybeRename(dw.name))
    case sp: Stop => sp.mapExpr(analyzeExpression)
    case a: Attach => a.mapExpr(analyzeExpression)
    case dr: DefRegister => dr.copy(name = maybeRename(dr.name)).mapExpr(analyzeExpression)
    case di: DefInstance => di.copy(name = maybeRename(di.name))
    case _ => s
  }

  override def run(c: Circuit): Circuit = c.mapModule {
    //Module(info: Info, name: String, ports: Seq[Port], body: Statement)
    case Module(info, name, ports, body) =>
      val moduleName = maybeRename(name)
      val newPorts = ports.map { p => p.copy(name = maybeRename(p.name)) }
      // look through the body
      val newBody = body.mapStmt(analyzeStatement)
      // return
      Module(info, moduleName, newPorts, newBody)

    //ExtModule(info: Info, name: String, ports: Seq[Port], defname: String, params: Seq[Param])
    case ExtModule(info, name , ports, defname, params) =>
      val extmodulename = maybeRename(name)
      val newPorts = ports.map { p => p.copy(name = maybeRename(p.name))}
      val newdefname = maybeRename(defname)
      ExtModule(info, extmodulename, newPorts, newdefname,params)

  }
}


