package essent.passes

import essent.Emitter._
import essent.Extract._

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.options.Dependency
import firrtl.passes._
import firrtl.Utils._


// This pass finesses the firrtl graph to make it easier to emit memory reads
// - the read port is defined as a node (memName.readPortName)
// - Pass 1) finds memories in the design
// - Pass 2) finds which signals are used as address for each read port
// - Pass 3) replaces address connections with SubAccesses into the memory
// - Pass 4) replaces references to read ports' .data with read port name
// FUTURE: consider merging internal passes to speed things up (4 passes -> 2)
// FUTURE: should respect enable for read ports

object FactorMemReads extends Pass {
  def desc = "Transforms mem read ports into SubAccesses for easier emission"

  override def prerequisites = Seq(Dependency(essent.passes.RegFromMem1))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def memHasRightParams(m: DefMemory) = {
    (m.readLatency == 0) && (m.readwriters.isEmpty)
  }

  def findReadPortAddrs(readPorts: Set[String])(s: Statement): Seq[(String,Expression)] = s match {
    case b: Block => b.stmts flatMap findReadPortAddrs(readPorts)
    case Connect(_, WSubField(WSubField(WRef(memName,_,_,_), portName, _, _), "addr", _, _), rhs) =>
      val fullPortName = memName + "." + portName
      if (readPorts.contains(fullPortName)) Seq((fullPortName, rhs))
      else Seq()
    case _ => Seq()
  }

  def replaceReadConnects(readPortAddrs: Map[String,Expression],
                          readPortTypes: Map[String,Type])(s: Statement): Statement = {
    val readConnectsReplaced = s match {
      case Connect(_, WSubField(WSubField(WRef(memName,_,_,_), portName, _, _), suffix, addrType, addrFlow), rhs) =>
        val fullPortName = memName + "." + portName
        if (readPortAddrs.contains(fullPortName)) {
          if (suffix == "addr") {
            val memRef = WRef(memName, readPortTypes(fullPortName), firrtl.MemKind, SinkFlow)
            val memRead = WSubAccess(memRef, readPortAddrs(fullPortName), readPortTypes(fullPortName), SourceFlow)
            DefNode(NoInfo, fullPortName, memRead)
          } else if (suffix == "en") EmptyStmt
          else s
        } else s
      case _ => s
    }
    readConnectsReplaced map replaceReadConnects(readPortAddrs, readPortTypes)
  }

  def replaceReadPortRefsStmt(readPortAddrs: Map[String,Expression])(s: Statement): Statement = {
    s map replaceReadPortRefsStmt(readPortAddrs) map replaceReadPortRefsExpr(readPortAddrs)
  }

  def replaceReadPortRefsExpr(readPortAddrs: Map[String,Expression])(e: Expression): Expression = {
    val refsReplaced = e match {
      case WSubField(WSubField(WRef(memName,_,_,_), portName, _, _), "data", dataType, dataFlow) => {
        val fullPortName = memName + "." + portName
        if (readPortAddrs.contains(fullPortName)) {
          WRef(fullPortName, dataType, firrtl.MemKind, dataFlow)
        } else e
      }
      case _ => e
    }
    refsReplaced map replaceReadPortRefsExpr(readPortAddrs)
  }

  def FactorMemReadsModule(m: Module): Module = {
    val memsInModule = findInstancesOf[DefMemory](m.body)
    memsInModule foreach {m =>
      if(!memHasRightParams(m)) throw new Exception(s"improper mem! $m")}
    val readPortTypes = (memsInModule flatMap {
      mem => mem.readers map { readPortName => (mem.name + "." + readPortName, mem.dataType) }
    }).toMap
    val readPorts = readPortTypes.keySet
    val readPortAddrs = (findReadPortAddrs(readPorts)(m.body)).toMap
    if (readPortAddrs.keySet != readPorts)
      throw new Exception("Mismatch between expected and found memory read ports")
    val memReadAddrsReplaced = replaceReadConnects(readPortAddrs, readPortTypes)(m.body)
    val memReadsReplaced = replaceReadPortRefsStmt(readPortAddrs)(memReadAddrsReplaced)
    Module(m.info, m.name, m.ports, squashEmpty(memReadsReplaced))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => FactorMemReadsModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
