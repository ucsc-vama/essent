package essent

import essent.Emitter._
import essent.Extract._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.Utils._

object RegFromMem1 extends Pass {
  def name = "Replaces single-element mems with a register"

  def replaceMems(memsToReplace: Set[String])(s: Statement): Statement = {
    val memsReplaced = s match {
      case mem: DefMemory => {
        if (memsToReplace.contains(mem.name)) {
          // FUTURE: should clock be something else?
          // aside: what clock is mem latency relative to?
          DefRegister(mem.info, mem.name, mem.dataType, UIntLiteral(0,IntWidth(1)),
                      UIntLiteral(0,IntWidth(1)), UIntLiteral(0,IntWidth(1)))
        } else s
      }
      case _ => s
    }
    memsReplaced map replaceMems(memsToReplace)
  }

  def grabMemConnects(s: Statement): Seq[(String, Expression)] = s match {
    case b: Block => b.stmts flatMap {s: Statement => grabMemConnects(s)}
    case c: Connect => {
      firrtl.Utils.kind(c.loc) match {
        case firrtl.MemKind => Seq((emitExpr(c.loc), c.expr))
        case _ => Seq()
      }
    }
    case _ => Seq()
  }

  def findWriteInputs(mems: Seq[DefMemory], body: Statement): Seq[(String,Expression)] = {
    val memConnects = grabMemConnects(body).toMap
    mems filter { !_.writers.isEmpty } map { 
      mem => (mem.name, memConnects(s"${mem.name}.${mem.writers.head}.data"))
    }
  }

  // drop mem connects
  def dropMemConnects(s: Statement): Statement = {
    val noConnects = s match {
      case c: Connect => {
        firrtl.Utils.kind(c.loc) match {
          case firrtl.MemKind => EmptyStmt
          case _ => s
        }
      }
      case _ => s
    }
    noConnects map dropMemConnects
  }

  // replace mem reads
  def replaceMemReadsStmt(memsToTypes: Map[String,Type])(s: Statement): Statement = {
    s map replaceMemReadsStmt(memsToTypes) map  replaceMemReadsExpr(memsToTypes)
  }
  def replaceMemReadsExpr(memsToTypes: Map[String,Type])(e: Expression): Expression = {
    val replaced = e match {
      case WSubField(WSubField(WRef(name: String, _, _, g: Gender),_,_,_),"data",_,_) => {
        if (memsToTypes.contains(name)) WRef(name, memsToTypes(name), firrtl.RegKind, g)
        else e
      }
      case _ => e
    }
    replaced map replaceMemReadsExpr(memsToTypes)
  }

  // insert reg write muxes

  // def replaceMemSigsStmt(memMap: Map[String,DefMemory])(s: Statement): Statement = {}
  // def replaceMemSigsExpr(memMap: Map[String,DefMemory])(e: Expression): Expression = {}

  def memReplaceModule(m: Module): Module = {
    val allMems = Extract.findMemory(m.body)
    // FUTURE: put in check to make sure latencies safe (& only 1 write port)
    // FUTURE: need to explicitly handle read enables?
    val singleElementMems = allMems filter { _.depth == 1}
    println(s"${m.name} ${singleElementMems.size}")
    val writeInputs = findWriteInputs(singleElementMems, m.body)
    val memMap = (singleElementMems map { mem => (mem.name, mem)}).toMap
    val memConnects = grabMemConnects(m.body).toMap
    val memsReplaced = replaceMems(memMap.keys.toSet)(m.body)
    val memConnectsRemoved = dropMemConnects(memsReplaced)
    val memsToTypes = (singleElementMems map { mem => (mem.name, mem.dataType)}).toMap
    val memReadsReplaced = replaceMemReadsStmt(memsToTypes)(memConnectsRemoved)
    Module(m.info, m.name, m.ports, squashEmpty(memReadsReplaced))
    // m
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => memReplaceModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}