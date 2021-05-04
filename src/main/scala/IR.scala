package essent.ir

import essent.Extract
import essent.MakeCondPart.{ConnectionMap, SignalTypeMap}
import essent.Util.StatementUtils
import firrtl._
import firrtl.ir._

import scala.+:

// ESSENT's additions to the IR for optimization

case class RegUpdate(info: Info, regRef: Expression, expr: Expression) extends Statement with HasInfo {
  def serialize: String =  s"${regRef.serialize} <= ${expr.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this.copy(regRef = f(regRef), expr = f(expr))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapInfo(f: Info => Info): Statement = this
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = {
    f(regRef)
    f(expr)
  }
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = f(info)
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = Unit
  def foreachString(f: String => Unit): Unit = Unit
  def foreachType(f: firrtl.ir.Type => Unit): Unit = Unit
}

case class MemWrite(info: Info,
                    memName: String,
                    portName: String,
                    wrEn: Expression,
                    wrMask: Expression,
                    wrAddr: Expression,
                    wrData: Expression) extends Statement with HasInfo {
  def serialize: String = s"if (${wrEn.serialize} && ${wrMask.serialize}) $memName[${wrAddr.serialize}] = ${wrData.serialize}"
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this.copy(wrEn = f(wrEn), wrMask = f(wrMask), wrAddr = f(wrAddr), wrData = f(wrData))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this.copy(memName = f(memName), portName = f(portName))
  def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  def nodeName(): String = s"$memName.$portName"
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = {
    f(wrEn)
    f(wrMask)
    f(wrAddr)
    f(wrData)
  }
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = f(info)
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = Unit
  def foreachString(f: String => Unit): Unit = {
    f(memName)
    f(portName)
  }
  def foreachType(f: firrtl.ir.Type => Unit): Unit = Unit
}

case class CondMux(info: Info, name: String, mux: Mux, tWay: Seq[Statement], fWay: Seq[Statement]) extends Statement with HasInfo {
  def serialize: String =  "conditional mux"
  def mapStmt(f: Statement => Statement): Statement = this.copy(tWay = tWay map f, fWay = fWay map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = Unit
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = f(info)
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = {
    tWay foreach f
    fWay foreach f
  }
  def foreachString(f: String => Unit): Unit = f(name)
  def foreachType(f: firrtl.ir.Type => Unit): Unit = Unit
}

/**
 * Conditional Partition
 * @param isRepeated if true, then the id refers to another existing partition* @param inputs
 * @param memberStmts if repeated, may be empty
 */
case class CondPart(
    info: Info,
    id: Int,
    alwaysActive: Boolean,
    isRepeated: Boolean,
    inputs: Set[String],
    memberStmts: Seq[Statement],
    outputsToDeclare: Map[String,firrtl.ir.Type],
    gcsmConnectionMap: ConnectionMap = Map.empty) extends Statement with HasInfo {
  /**
   * Get the GCSM info, if applicable
   */
  lazy val gcsm: Option[GCSMInfo] = this.getInfoByType[GCSMInfo]()

  def serialize: String = s"CondPart #$id"
  def mapStmt(f: Statement => Statement): Statement = this.copy(memberStmts = memberStmts map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this.copy(inputs = inputs map f)
  def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = Unit
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = f(info)
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = memberStmts foreach f
  def foreachString(f: String => Unit): Unit = inputs foreach f
  def foreachType(f: firrtl.ir.Type => Unit): Unit = Unit
}

/**
 * Tag to apply to statements to denote that it belongs to the GCSM.
 * @param modName The module in question
 * @param instanceName The name of this particular instantiation of the GCSM
 */
case class GCSMInfo(modName: String, instanceName: String) extends Info {
  override def toString: String = s"@[Instance '$instanceName' GCSM $modName]"
  override def ++(that: Info): Info = if (that == NoInfo) this else MultiInfo(Seq(this, that))
}

object GCSMInfo {
  /**
   * Is the given statement a GCSM-related one?
   * @return The GCSMInfo, if any
   */
  def is(stmt: Statement): Option[GCSMInfo] = stmt.getInfoByType[GCSMInfo]()
}

/**
 * Wrapper for a [[WRef]] to denote that it's part of the GCSM
 * @param ref The original reference
 * @param gcsmInstanceName The name of the GCSM instance
 */
// TODO - make this a wrapper for WRef, can delete the externalReference since it's probably not needed?
case class GCSMSignalReference(ref: WRef, gcsmInstanceName: String) extends Expression {
  /**
   * The short name of this signal, suitable for use in the GCSM struct
   */
  val shortName: String = ref.name match {
    case Extract.signalNamePat(_, signalName) => signalName
  }

  override def foreachExpr(f: Expression => Unit): Unit = Unit
  override def foreachType(f: Type => Unit): Unit = Unit
  override def foreachWidth(f: Width => Unit): Unit = Unit
  override def mapExpr(f: Expression => Expression): Expression = this
  override def mapType(f: Type => Type): Expression = this
  override def mapWidth(f: Width => Width): Expression = this
  override def serialize: String = s"signal reference: $shortName in ${gcsmInstanceName}"
  override def tpe: Type = UnknownType

  // When comparing signal references, only the shortName is important
  override def hashCode(): Int = shortName.hashCode()
  override def equals(that: Any): Boolean = that match {
    case x: GCSMSignalReference => x.shortName == this.shortName
    case x: String => x == this.shortName || x == this.ref.name
    case _ => false
  }
}

@Deprecated
case class FakeConnection(source: String, dest: String, tpe: Type) extends Statement {
 //require(this.getInfoByType[GCSMInfo]().isDefined, "must have a GCSM info here")

  override def mapStmt(f: Statement => Statement): Statement = this
  override def mapExpr(f: Expression => Expression): Statement = this
  override def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  override def mapString(f: String => String): Statement = this.copy(source = f(source), dest = f(dest))
  override def mapInfo(f: Info => Info): Statement = this
  override def foreachStmt(f: Statement => Unit): Unit = Unit
  override def foreachExpr(f: Expression => Unit): Unit = Unit
  override def foreachType(f: Type => Unit): Unit = f(tpe)
  override def foreachString(f: String => Unit): Unit = {
    f(source)
    f(dest)
  }
  override def foreachInfo(f: Info => Unit): Unit = Unit
  override def serialize: String = s"FakeConnect: $source -> $dest ($tpe)"
}

/**
 * Blackbox connection node for the secondary GCSM instance connections
 * @param name the name of the signal
 * @param flow from the perspective of the main design: sink = instance input; source = instance output
 */
case class GCSMBlackboxConnection(info: Info, name: String, tpe: Type, flow: Flow) extends Statement with HasInfo {
  // the flow must be either source or sink
  require(flow == SourceFlow || flow == SinkFlow, "this only understands source or sink flows")

  override def mapStmt(f: Statement => Statement): Statement = this
  override def mapExpr(f: Expression => Expression): Statement = this
  override def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  override def mapString(f: String => String): Statement = this.copy(name = f(name))
  override def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  override def foreachStmt(f: Statement => Unit): Unit = Unit
  override def foreachExpr(f: Expression => Unit): Unit = Unit
  override def foreachType(f: Type => Unit): Unit = f(tpe)
  override def foreachString(f: String => Unit): Unit = f(name)
  override def foreachInfo(f: Info => Unit): Unit = f(info)
  override def serialize: String = s"GCSMBlackboxConnection: $flow for $name"
}