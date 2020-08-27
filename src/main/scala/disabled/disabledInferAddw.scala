package disabled

import collection.mutable.HashMap

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._
import firrtl.PrimOps._
import firrtl.Utils._


// Replaces a tail following an add with an addw if:
// - result of add is used only in the one tail
// - tail only clips top bit
// - also does sub -> subw


object InferAddw extends Pass {
  def desc = "Replace tail on add results with addw (or sub with subw)"

  val WRefCounts = HashMap[String, Int]()

  // return names of all nodes with add expressions
  def findAddSigs(s: Statement): Seq[(String,DoPrim)] = s match {
    case b: Block => b.stmts flatMap findAddSigs
    case DefNode(_, name: String, primE: DoPrim) => primE.op match { 
      case Add => Seq((name, primE copy (tpe = oneNarrower(primE.tpe))))
      // case Sub => Seq((name, primE copy (tpe = oneNarrower(primE.tpe))))
      case _ => Seq()
    }
    case _ => Seq()
  }

  def countWRefsExpr(addSigs: Set[String])(e: Expression): Expression = {
    e match {
      case WRef(name, _, _, _) => {
        if (addSigs.contains(name)) WRefCounts(name) = WRefCounts.getOrElse(name,0) + 1
      }
      case _ => e
    }
    e map countWRefsExpr(addSigs)
  }

  def countWRefsStmt(addSigs: Set[String])(s: Statement): Statement = {
    s map countWRefsStmt(addSigs) map countWRefsExpr(addSigs)
  }

  // return names of all nodes that tail an add expressions
  def findDependentTails(addSigs: Set[String])(s: Statement): Seq[(String,String)] = {
    s match {
      case b: Block => b.stmts flatMap findDependentTails(addSigs)
      case DefNode(_, tName: String, primE: DoPrim) => primE.op match { 
        case Tail => {
          val eName = primE.args.head match { case w: WRef => w.name }
          if ((addSigs.contains(eName)) && (primE.consts.head == 1) && (bitWidth(primE.tpe) == 64))
            Seq((tName, eName))
          else Seq()
        }
        case _ => Seq()
      }
      case _ => Seq()
    }
  }

  def oneNarrower(tpe: Type): Type = tpe match {
    case UIntType(w) => UIntType(w - IntWidth(1))
    case SIntType(w) => SIntType(w - IntWidth(1))
    case _ => throw new Exception("can't narrow a non-ground type!")
  }

  def convertExpToW(primE: DoPrim): DoPrim = {
    val newOp = primE.op match {
      case Add => Addw
      // case Sub => Subw
    }
    primE copy (op = newOp)
  }

  def replaceInferAddwStmt(tailMap: Map[String,DoPrim], addsToRemove: Set[String])(s: Statement): Statement = {
    val replaced = s match {
      case DefNode(info, nodeName: String, primE: DoPrim) => primE.op match { 
        case Tail => {
          if (tailMap.contains(nodeName))
            DefNode(info, nodeName, convertExpToW(tailMap(nodeName)))
          else s
        }
        case Add => {
          if (addsToRemove.contains(nodeName)) EmptyStmt
          else s
        }
        // case Sub => {
        //   if (addsToRemove.contains(nodeName)) EmptyStmt
        //   else s
        // }
        case _ => s
      }
      case _ => s
    }
    replaced map replaceInferAddwStmt(tailMap, addsToRemove)
  }

  def InferAddwModule(m: Module): Module = {
    val addMap = findAddSigs(m.body).toMap
    WRefCounts.clear()
    m.body map countWRefsStmt(addMap.keySet)
    val singleUseAddSigs = addMap.filter { case (k, v) => WRefCounts(k) == 1 }
    val tailPairs = findDependentTails(singleUseAddSigs.keySet)(m.body)
    val tailMap = (tailPairs map { case (tailSig: String, addSig: String) =>
      (tailSig, addMap(addSig)) }).toMap
    val addsToRemove = (tailPairs map { _._2 }).toSet
    val newBody = m.body map replaceInferAddwStmt(tailMap, addsToRemove)
    Module(m.info, m.name, m.ports, squashEmpty(newBody))
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module => InferAddwModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
