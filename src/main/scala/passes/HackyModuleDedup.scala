package essent.passes

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
 *
 * This is similar to [[firrtl.transforms.DedupModules]] but that one
 * for some reason doesn't actually dedup everything it could?
 * If that's fixed then this can be removed.
 */
@Deprecated
object HackyModuleDedup extends Pass with DependencyAPIMigration {
  // only want the statement contents, sometimes the info is different between different copies of the same module
  private def getStatementBytes(s: Statement) = s.mapInfo(_ => NoInfo).serialize.getBytes
  private def hashStatement(s: Statement) = BigInt(1,
    MessageDigest.getInstance("SHA-256")
      .digest(getStatementBytes(s)))

  override def run(c: Circuit): Circuit = {
    // first find modules we want
    val modulesToReplace = c.modules.par.toStream.flatMap({
      case ExtModule(info, name, ports, defname, params) => None
      case Module(info, name, _, body) =>
        Some(hashStatement(body) -> name)
    }).toMapOfLists.filter({ // only want modules where more than 1 have same content
      case (_, names) => names.size > 1
    }).flatMap({
      case (hash, names) => names.tail.map(n => n -> names.head)
    })

    // next traverse all modules replacing the redundant names
    def replaceStatement(s: Statement): Statement = s match {
      case d: DefInstance if modulesToReplace.contains(d.module) =>
        d.copy(module = modulesToReplace(d.module))
      case d: WDefInstance if modulesToReplace.contains(d.module) =>
        d.copy(module = modulesToReplace(d.module))
      case _ => s.mapStmt(replaceStatement)
    }

    logger.info(s"Found ${modulesToReplace.size} modules to replace")

    if (modulesToReplace.nonEmpty) {
      val newModules = c.modules.par.toStream
        .filter({
          case _: ExtModule => true // always include these
          case Module(_, name, _, _) => !modulesToReplace.contains(name) // keep only the not redundant modules
        })
        .map(_.mapStmt(replaceStatement))
        .toVector

      // possible that we now have more things to dedup if higher-level modules instantiated
      // stuff that was just removed
      run(c.copy(modules = newModules))
    } else {
      // once there are no more modules to replace we are done
      c
    }
  }
}
