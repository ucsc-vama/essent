package essent.passes

import essent.Extract.findInstancesOf
import firrtl._
import firrtl.ir._
import firrtl.passes._

import collection.mutable.Map

object CheckStatistics extends Pass{
  def desc = "Check node type and count"

  override def prerequisites = firrtl.stage.Forms.LowFormOptimized

  override def invalidates(a: Transform): Boolean = false


  def collectNodeType(dat: Map[String, Int])(s: Statement): Seq[Nothing] = {
    s match {
      case b: Block => {
        b.stmts flatMap collectNodeType(dat)
      }
      case other => {
        val nodeName = other.getClass.getName()
        if (dat contains nodeName) {
          dat(nodeName) += 1
        } else {
          dat(nodeName) = 1
        }
      }
    }
    Seq()

  }

  override def run(c: Circuit): Circuit = {
    val dat = collection.mutable.Map[String, Int]()

    c.modules.foreach {
      case m: Module => {
        m.body match {
          case s: Statement => collectNodeType(dat)(s)
          case _ => 0
        }
      }
      case e: ExtModule => 0
    }

    for ((k, v) <- dat) {
      println(s"$k : $v")
    }
    c
  }
}