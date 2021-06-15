package essent.passes

import essent.Extract
import essent.Extract.{countStatements, findAllModuleInstances, findModule}
import essent.Util.IterableUtils
import firrtl.analyses.InstanceGraph
import firrtl.annotations.{Annotation, ModuleTarget, SingleTargetAnnotation}
import firrtl.{CircuitState, DependencyAPIMigration, Transform, WDefInstance}
import firrtl.ir.{Block, Circuit, EmptyStmt, IsInvalid, Module, Statement, Stop}
import firrtl.passes.Pass
import firrtl.stage.Forms.LowFormMinimumOptimized
import firrtl.stage.TransformManager.TransformDependency


/**
 * Identify the Greatest Common Shared Module, and annotate it
 */
object IdentifyGCSM extends Transform with DependencyAPIMigration {
  override def name: String = "IdentifyGCSM"

  override def invalidates(a: Transform): Boolean = false

  //override def optionalPrerequisites: Seq[TransformDependency] = LowFormMinimumOptimized

  /**
   * Similar to [[Extract.countStatements()]] but doesn't recurse into instantiations
   * @param s
   * @return
   */
  private def countStatementsOnly(s: Statement): Int = s match {
    case b: Block => b.stmts.map(countStatementsOnly).sum
    case EmptyStmt => 0
    case i: IsInvalid => 0
    case s: Stop => 0
    case _: WDefInstance => 0
    case _ => 1
  }

  override def execute(state: CircuitState): CircuitState = {
    type Result = (Module, (Int, Int))

    val moduleUsage = findAllModuleInstances(state.circuit)
      .toMapOfLists
      .toSeq
      .flatMap({
        case (modName, instanceNames) if instanceNames.size > 1 => findModule(modName, state.circuit) match {
          case m: Module => Some(m -> (
            instanceNames.size,
            countStatements(m.body, state.circuit),
            countStatementsOnly(m.body)
          ))
          case _ => None
        }
        case _ => None
      })
      .sortBy({
        case (_, (numInstances, stmtsPerInstance, _)) => numInstances * stmtsPerInstance
      })(Ordering[Int].reverse)

    val newAnno = moduleUsage.headOption map {
      case(gcsmMod, _) => ModuleIsGCSM(ModuleTarget(state.circuit.main, gcsmMod.name))
    }

    logger.info("--- GCSM Module Result: ---")
    logger.info("modName,numInstances,stmtsPerInstance,stmtsPerInstanceOnly")
    if (moduleUsage.isEmpty) logger.info("No repeated modules")
    logger.info(moduleUsage.map({
      case (module, (numInstances, stmtsPerInstance, stmtsPerInstanceOnly)) =>
        s"${module.name},$numInstances,$stmtsPerInstance,$stmtsPerInstanceOnly"
    }).mkString("\n"))
    logger.info("---------------------")

    state.copy(annotations = state.annotations ++ newAnno)
  }

  case class ModuleIsGCSM(override val target: ModuleTarget) extends SingleTargetAnnotation[ModuleTarget] {
    override def duplicate(n: ModuleTarget): Annotation = this.copy(target = n)
  }
}
