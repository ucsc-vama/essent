package essent.ir

import firrtl._
import firrtl.ir._

// ESSENT's additions to the IR for optimization

case class RegUpdate(info: Info, regRef: Expression, expr: Expression) extends Statement {
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

case class MemWrite(memName: String,
                    portName: String,
                    wrEn: Expression,
                    wrMask: Expression,
                    wrAddr: Expression,
                    wrData: Expression) extends Statement {
  def serialize: String = s"if (${wrEn.serialize} && ${wrMask.serialize}) $memName[${wrAddr.serialize}] = ${wrData.serialize}"
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = {
    MemWrite(memName, portName, f(wrEn), f(wrMask), f(wrAddr), f(wrData))
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

case class CondMux(name: String, mux: Mux, tWay: Seq[Statement], fWay: Seq[Statement]) extends Statement {
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
    id: Int,
    alwaysActive: Boolean,
    inputs: Seq[String],
    memberStmts: Seq[Statement],
    outputsToDeclare: Map[String,firrtl.ir.Type]) extends Statement {
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
