package essent.passes

import essent.Emitter._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.options.Dependency
import firrtl.passes._
import firrtl.Utils._


object RegFromMem1 extends Pass {
  def desc = "Replaces single-element mems with a register"

  override def prerequisites = Seq(Dependency(essent.passes.NoClockConnects))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def memHasRightParams(m: DefMemory) = {
    (m.depth == 1) && (m.writeLatency == 1) && (m.readLatency == 0) &&
      (m.readwriters.isEmpty) && (m.writers.size <= 1)
  }

  def grabMemConnects(s: Statement): Seq[(String, Expression)] = s match {
    case b: Block => b.stmts flatMap grabMemConnects
    case c: Connect if firrtl.Utils.kind(c.loc) == firrtl.MemKind => Seq(emitExpr(c.loc) -> c.expr)
    case _ => Seq()
  }

  def dropMemConnects(memsToReplace: Set[String])(s: Statement): Statement = {
    val noConnects = s match {
      case Connect(_,WSubField(WSubField(WRef(name: String,_,_,_),_,_,_),_,_,_),_) => {
        if (memsToReplace.contains(name)) EmptyStmt
        else s
      }
      case _ => s
    }
    noConnects map dropMemConnects(memsToReplace)
  }

  // replace mem def's and mem reads
  def replaceMemsStmt(memsToTypes: Map[String,Type])(s: Statement): Statement = {
    val memsReplaced = s match {
      case mem: DefMemory if (memsToTypes.contains(mem.name)) => {
        // FUTURE: what is clock for a mem? assuming it is based on surrounding context
        DefRegister(mem.info, mem.name, mem.dataType, WRef("clock", ClockType, PortKind),
                    UIntLiteral(0,IntWidth(1)), UIntLiteral(0,IntWidth(1)))
      }
      case _ => s
    }
    memsReplaced map replaceMemsStmt(memsToTypes) map replaceMemsExpr(memsToTypes)
  }

  def replaceMemsExpr(memsToTypes: Map[String,Type])(e: Expression): Expression = {
    val replaced = e match {
      case WSubField(WSubField(WRef(name: String, _, _, f: Flow),_,_,_),"data",_,_) => {
        if (memsToTypes.contains(name)) WRef(name, memsToTypes(name), firrtl.RegKind, f)
        else e
      }
      case _ => e
    }
    replaced map replaceMemsExpr(memsToTypes)
  }

  // insert reg write muxes
  def generateRegUpdates(memsToReplace: Seq[DefMemory], body: Statement): Seq[Statement] = {
    val memConnects = grabMemConnects(body).toMap
    val memsWithWrites = memsToReplace filter { _.writers.nonEmpty }
    memsWithWrites flatMap { mem => mem.writers map { writePortName => {
      val selfRef = WRef(mem.name, mem.dataType, firrtl.RegKind, firrtl.DuplexFlow)
      val enSig = memConnects(s"${mem.name}.$writePortName.en")
      val wrDataSig = memConnects(s"${mem.name}.$writePortName.data")
      val wrEnableMux = Mux(enSig, wrDataSig, selfRef, mem.dataType)
      Connect(NoInfo, selfRef, wrEnableMux)
    }}}
  }

  def memReplaceModule(m: Module): Module = {
    val allMems = essent.Extract.findInstancesOf[DefMemory](m.body)
    // FUTURE: need to explicitly handle read enables?
    val singleElementMems = allMems filter memHasRightParams
    if (singleElementMems.isEmpty) m
    else {
      val memNamesToReplace = (singleElementMems map { _.name }).toSet
      val memConnectsRemoved = squashEmpty(dropMemConnects(memNamesToReplace)(m.body))
      val memsToTypes = (singleElementMems map { mem => (mem.name, mem.dataType)}).toMap
      val memsReplaced = replaceMemsStmt(memsToTypes)(memConnectsRemoved)
      val regUpdateStmts = generateRegUpdates(singleElementMems, m.body)
      val newBlock = Block(Seq(memsReplaced) ++ regUpdateStmts)
      m.copy(body = newBlock)
    }
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => memReplaceModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}