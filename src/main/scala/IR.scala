package essent.ir

import essent.{Emitter, Extract}
import essent.MakeCondPart.ConnectionMap
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
  def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
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
  def mapString(f: String => String): Statement = this.copy(memName = f(memName))
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
    f(portName)
  }
  def foreachType(f: firrtl.ir.Type => Unit): Unit = Unit
}

case class CondMux(info: Info, name: String, mux: Mux, tWay: Seq[Statement], fWay: Seq[Statement]) extends Statement with HasInfo with HasName {
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
 * @param repeatedMainCp if this is a repeated partition, this points to the actual CondPart
 * @param memberStmts if repeated, may be empty
 */
case class CondPart(
    info: Info,
    id: Int,
    alwaysActive: Boolean,
    inputs: Set[String],
    memberStmts: Seq[Statement],
    outputsToDeclare: Map[String,firrtl.ir.Type],
    repeatedMainCp: Option[CondPart] = None) extends Statement with HasInfo {
  /**
   * Get the GCSM info, if applicable
   */
  lazy val gcsm: Option[GCSMInfo] = this.getInfoByType[GCSMInfo]()

  /**
   * The ID of the main partition, if defined by `repeatedMainCp` or else this ID.
   * @note Will not terminate if there's a loop formed by `repeatedMainCp`
   */
  lazy val mainId: Int = repeatedMainCp.map(_.mainId).getOrElse(id)

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

/**
 * Alternative for a [[WRef]] to denote that it's part of the GCSM
 * @param name The name of the signal (with GCSM instance prefix removed)
 * @param tpe The type of the signal
 */
case class GCSMSignalPlaceholder(name: String, tpe: firrtl.ir.Type) extends Expression with HasName with Ordered[GCSMSignalPlaceholder] {
  override def foreachExpr(f: Expression => Unit): Unit = Unit
  override def foreachType(f: Type => Unit): Unit = f(tpe)
  override def foreachWidth(f: Width => Unit): Unit = Unit
  override def mapExpr(f: Expression => Expression): Expression = this
  override def mapType(f: Type => Type): Expression = this.copy(tpe = f(tpe))
  override def mapWidth(f: Width => Width): Expression = this
  override def serialize: String = s"GCSM Placeholder signal ($name): $tpe"
  override def compare(that: GCSMSignalPlaceholder): Int = this.name compare that.name

  /**
   * Get the fully-qualified signal name given some prefix
   */
  def getFullyQualifiedName(prefix: String): String = prefix + name
}
