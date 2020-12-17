package essent

import logger.LazyLogging

/**
 *
 * @param sg
 * @param moduleInstanceGraph
 */
class OptDoRepeated(private val sg: StatementGraph, private val moduleInstanceGraph: ModuleInstanceGraph) extends LazyLogging {

}

object OptDoRepeated {
    def apply(sg: StatementGraph, moduleInstanceGraph: ModuleInstanceGraph): OptDoRepeated = new OptDoRepeated(sg, moduleInstanceGraph)
}