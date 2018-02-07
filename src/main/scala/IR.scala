package essent.ir

import firrtl._
import firrtl.ir._

// ESSENT's additions to the IR for optimization

case class MuxShadowed(name: String, mux: Mux, tShadow: Seq[Statement], fShadow: Seq[Statement]) extends Statement {
  def serialize: String =  "shadow mux"
  // FUTURE probably shouldn't have all maps be identity
  def mapStmt(f: Statement => Statement): Statement = this.copy(tShadow = tShadow map f, fShadow = fShadow map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
}

case class ActivityZone(
    name:String,
    inputs: Seq[String],
    members: Seq[Statement],
    outputConsumers: Map[String,Seq[String]],
    outputTypes: Map[String,firrtl.ir.Type]) extends Statement {
  def serialize: String =  "activity zone"
  // FUTURE probably shouldn't have all maps be identity
  def mapStmt(f: Statement => Statement): Statement = this.copy(members = members map f)
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this
  def mapString(f: String => String): Statement = this
}
