package essent.passes

import essent.Extract
import essent.Util.IterableUtils
import firrtl.{DependencyAPIMigration, WDefInstance}
import firrtl.ir._
import firrtl.passes.Pass

import java.security.MessageDigest

/**
 * For some reason Chisel doesn't always deduplicate modules even
 * though they're the same FIRRTL. To avoid having to debug that
 * can of worms, this pass just hashes the modules and finds
 * identical ones.
 */
object HackyChiselDedup extends Pass with DependencyAPIMigration {
  private def hashStatement(s: Statement) = BigInt(1,
    MessageDigest.getInstance("MD5")
      .digest(s.serialize.getBytes))

  override def run(c: Circuit): Circuit = {
    // first find modules we want
    val modulesToReplace = c.modules.par.flatMap({
      case ExtModule(info, name, ports, defname, params) => None
      case Module(info, name, _, body) =>
        Some(hashStatement(body) -> name)
    }).toStream.toMapOfLists.filter({ // only want modules where more than 1 have same content
      case (_, names) => names.size > 1
    }).flatMap({
      case (hash, names) => names.tail.map(n => n -> names.head)
    })

    // next traverse all modules replacing the redundant names
    def replaceStatement(s: Statement): Statement = s match {
      case b: Block => b.mapStmt(replaceStatement)
      case d: DefInstance if modulesToReplace.contains(d.module) =>
        d.copy(name = modulesToReplace(d.name))
      case d: WDefInstance if modulesToReplace.contains(d.module) =>
        d.copy(name = modulesToReplace(d.name))
      case _ => s
    }
    val newModules = c.modules.par
      .filter({
        case _: ExtModule => true // always include these
        case Module(_, name, _, _) => !modulesToReplace.contains(name)
      })
      .map(_.mapStmt(replaceStatement))
      .toVector

    c.copy(modules = newModules)
  }
}
