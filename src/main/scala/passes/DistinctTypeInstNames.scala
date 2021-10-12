package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.passes._


object DistinctTypeInstNames extends Pass {
  def desc = "Ensures modules are instantiations don't have same name as type"
  val suffix = "$$inst"

  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def findMatchingInstNames(moduleNames: Set[String])(s: Statement): Seq[String] = s match {
    case b: Block => b.stmts flatMap findMatchingInstNames(moduleNames)
    case wd: WDefInstance if (moduleNames(wd.name)) => Seq(wd.name)
    case _ => Seq()
  }

  def renameInstNamesStmt(toRename: Set[String])(s: Statement): Statement = {
    val renamed = s match {
      case wd: WDefInstance if (toRename(wd.name))=> wd.copy(name = wd.name + suffix)
      case _ => s
    }
    renamed map renameInstNamesStmt(toRename) map renameInstNamesExpr(toRename)
  }

  def renameInstNamesExpr(toRename: Set[String])(e: Expression): Expression = {
    val renamed = e match {
      case w: WRef if (toRename(w.name)) => w.copy(name = w.name + suffix)
      case _ => e
    }
    renamed map renameInstNamesExpr(toRename)
  }

  def distinctifyModule(m: Module, moduleNames: Set[String]): Module = {
    val dupeNamesToRename = findMatchingInstNames(moduleNames)(m.body).toSet
    m.copy(body = renameInstNamesStmt(dupeNamesToRename)(m.body))
  }

  def run(c: Circuit): Circuit = {
    val allModuleTypeNames = (c.modules.map { _.name }).toSet
    val modulesx = c.modules.map {
      case m: Module => distinctifyModule(m, allModuleTypeNames)
      case m: ExtModule => m
    }
    Circuit(c.info, modulesx, c.main)
  }
}
