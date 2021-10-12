package essent.passes

import essent.ir._
import essent.Extract._

import firrtl._
import firrtl.ir._
import firrtl.options.Dependency
import firrtl.passes._
import firrtl.Utils._


// Inserts MemWrite (custom) FIRRTL nodes into the graph and removes unneeded connects
// - Pass 1) finds memories in the design
// - Pass 2) finds associated signals (.en, .addr, .data, .mask)
// - Pass 3) removes connects to associated signals
// - Pass 4) inserts new MemWrite FIRRTL nodes
// FUTURE: consider merging internal passes to speed things up (4 passes -> 2)

object FactorMemWrites extends Pass {
  def desc = "Transforms mem write ports into MemWrite for easier emission"

  override def prerequisites = Seq(Dependency(essent.passes.RegFromMem1))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def memHasRightParams(m: DefMemory) = {
    (m.writeLatency == 1) && (m.readwriters.isEmpty)
  }

  def findWritePortExprs(writePorts: Set[String])(s: Statement): Seq[(String, Expression)] = s match {
    case b: Block => b.stmts flatMap findWritePortExprs(writePorts)
    case Connect(_, WSubField(WSubField(WRef(memName,_,_,_), portName, _, _), suffix, _, _), rhs) =>
      val fullPortName = memName + "." + portName
      if (((suffix == "en") || (suffix == "addr") || (suffix == "data") || (suffix == "mask")) && 
          writePorts.contains(fullPortName))
        Seq((s"$fullPortName.$suffix", rhs))
      else Seq()
    case _ => Seq()
  }

  def removeWritePortExpr(writePorts: Set[String])(s: Statement): Statement = s match {
    case b: Block => b.copy(stmts = b.stmts map removeWritePortExpr(writePorts))
    case Connect(_, WSubField(WSubField(WRef(memName,_,_,_), portName, _, _), suffix, _, _), rhs) =>
      val fullPortName = memName + "." + portName
      if (((suffix == "en") || (suffix == "addr") || (suffix == "data") || (suffix == "mask")) &&
          writePorts.contains(fullPortName))
        EmptyStmt
      else s
    case _ => s
  }

  def generateMemWrites(memories: Seq[DefMemory],
                        writePortSigs: Map[String, Expression]): Seq[Statement] = {
    memories flatMap { mem => {
      mem.writers map { writePortName => {
        val wrEnExpr = writePortSigs(s"${mem.name}.$writePortName.en")
        val wrMaskExpr = writePortSigs(s"${mem.name}.$writePortName.mask")
        val wrAddrExpr = writePortSigs(s"${mem.name}.$writePortName.addr")
        val wrDataExpr = writePortSigs(s"${mem.name}.$writePortName.data")
        MemWrite(mem.name, writePortName, wrEnExpr, wrMaskExpr, wrAddrExpr, wrDataExpr)
      }}
    }}
  }

  def FactorMemWritesModule(m: Module): Module = {
    val memsInModule = findInstancesOf[DefMemory](m.body)
    memsInModule foreach {m =>
      if(!memHasRightParams(m)) throw new Exception(s"improper mem! $m")}
    val writePortNames = (memsInModule flatMap { mem => mem.writers map { mem.name + "." +  _ }}).toSet
    val writePortSigs = (findWritePortExprs(writePortNames)(m.body)).toMap
    val memWritePortSigsRemoved = removeWritePortExpr(writePortNames)(m.body)
    val memWrites = generateMemWrites(memsInModule, writePortSigs)
    m.copy(body = Block(Seq(squashEmpty(memWritePortSigsRemoved)) ++ memWrites))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => FactorMemWritesModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
