package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.passes._


object ReplaceAsyncRegs extends Pass {
  def desc = "Replaces AsyncResetReg (black-box) with non-external module that behaves the same"
  // this pass is inspired by firebox/sim/src/main/scala/passes/AsyncResetReg.scala

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def isCorrectAsyncRegModule(em: ExtModule): Boolean = {
    val nameCorrect = em.defname == "AsyncResetReg"
    val portNames = em.ports map { _.name }
    val portsCorrect = portNames == Seq("rst", "clk", "en", "q", "d")
    nameCorrect && portsCorrect
  }

  def generateReplacementModule(em: ExtModule): Module = {
    logger.info(s"Replacing ${em.name} (${em.defname})")
    val oneBitType = UIntType(IntWidth(1))
    val zero = UIntLiteral(0,IntWidth(1))
    val reg = DefRegister(NoInfo, "r", oneBitType, WRef("clk", ClockType, PortKind, SourceFlow), zero, zero)
    val resetMux = Mux(WRef("rst", oneBitType, PortKind, SourceFlow),
                       zero,
                       WRef("enMux", oneBitType, NodeKind, SourceFlow), oneBitType)
    val enableMux = Mux(WRef("en", oneBitType, PortKind, SourceFlow),
                        WRef("d", oneBitType, PortKind, SourceFlow),
                        WRef(reg), oneBitType)
    val enableMuxStmt = DefNode(NoInfo, "enMux", enableMux)
    val resetMuxStmt = DefNode(NoInfo, "resetMux", resetMux)
    val connectToReg = Connect(NoInfo, WRef(reg), WRef("resetMux", oneBitType, NodeKind, SourceFlow))
    val connectFromReg = Connect(NoInfo, WRef("q", oneBitType, PortKind, SinkFlow), WRef(reg))
    val bodyStmts = Seq(reg, enableMuxStmt, resetMuxStmt, connectToReg, connectFromReg)
    Module(em.info, em.name, em.ports, Block(bodyStmts))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case em: ExtModule if isCorrectAsyncRegModule(em) => generateReplacementModule(em)
      case m => m
    }
    Circuit(c.info, modulesx, c.main)
  }
}
