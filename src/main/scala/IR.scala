package essent.ir

import firrtl._
import firrtl.ir._

// ESSENT's additions to the IR for optimization

case class RegUpdate(info: Info, regRef: Expression, expr: Expression) extends Statement with HasInfo {
  def serialize: String =  s"${regRef.serialize} <= ${expr.serialize}" + info.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this.copy(regRef = f(regRef), expr = f(expr))
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapInfo(f: Info => Info): Statement = this
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = ???
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = ???
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = ???
  def foreachString(f: String => Unit): Unit = ???
  def foreachType(f: firrtl.ir.Type => Unit): Unit = ???
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
  def mapExpr(f: Expression => Expression): Statement = {
    MemWrite(info, memName, portName, f(wrEn), f(wrMask), f(wrAddr), f(wrData))
  }
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapInfo(f: Info => Info): Statement = this
  def nodeName(): String = s"$memName.$portName"
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = ???
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = ???
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = ???
  def foreachString(f: String => Unit): Unit = ???
  def foreachType(f: firrtl.ir.Type => Unit): Unit = ???
}

case class CondMux(info: Info, name: String, mux: Mux, tWay: Seq[Statement], fWay: Seq[Statement]) extends Statement with HasInfo {
  def serialize: String =  "conditional mux"
  def mapStmt(f: Statement => Statement): Statement = this.copy(tWay = tWay map f, fWay = fWay map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapInfo(f: Info => Info): Statement = this
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = ???
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = ???
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = ???
  def foreachString(f: String => Unit): Unit = ???
  def foreachType(f: firrtl.ir.Type => Unit): Unit = ???
}

case class CondPart(
    info: Info,
    id: Int,
    alwaysActive: Boolean,
    inputs: Seq[String],
    memberStmts: Seq[Statement],
    outputsToDeclare: Map[String,firrtl.ir.Type]) extends Statement with HasInfo {
  def serialize: String = s"CondPart #$id"
  def mapStmt(f: Statement => Statement): Statement = this.copy(memberStmts = memberStmts map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
  def mapInfo(f: Info => Info): Statement = this
  def foreachExpr(f: firrtl.ir.Expression => Unit): Unit = ???
  def foreachInfo(f: firrtl.ir.Info => Unit): Unit = ???
  def foreachStmt(f: firrtl.ir.Statement => Unit): Unit = ???
  def foreachString(f: String => Unit): Unit = ???
  def foreachType(f: firrtl.ir.Type => Unit): Unit = ???
}

/**
 * Module tag to denote the repeated module instances
 * @param modName
 */
case class ModuleTagInfo(modName: String) extends Info {
  override def toString: String = "@[Partition: " + modName + "]"
  override def ++(that: Info): Info = if (that == NoInfo) this else MultiInfo(Seq(this, that))
}

/**
 * Denotes that this is an instantiation of a repeated module.
 *
 * @param info
 * @param name
 * @param module
 * @param tpe
 */
case class DefRepeatedInstance(info: Info, name: String, module: String, tpe: Type)
  extends Statement with IsDeclaration {
  def serialize: String = s"repeated_inst $name of $module" + info.serialize
  def mapExpr(f: Expression => Expression): Statement = this
  def mapStmt(f: Statement => Statement): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(tpe = f(tpe))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def mapInfo(f: Info => Info): Statement = this.copy(f(info))
  def foreachStmt(f: Statement => Unit): Unit = Unit
  def foreachExpr(f: Expression => Unit): Unit = Unit
  def foreachType(f: Type => Unit): Unit = f(tpe)
  def foreachString(f: String => Unit): Unit = f(name)
  def foreachInfo(f: Info => Unit): Unit = f(info)
}

object DefRepeatedInstance {
  /**
   * Turn a [[WDefInstance]] into a DefRepeatedInstance
   * @param orig
   * @return
   */
  def apply(orig: WDefInstance): DefRepeatedInstance = new DefRepeatedInstance(orig.info, orig.name, orig.module, orig.tpe)
}