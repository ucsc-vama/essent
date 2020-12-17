package essent

import essent.Graph.NodeID
import firrtl.WDefInstance
import firrtl.ir._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Represents the graph of unique module instantiations for a given circuit
 * Node = Module
 * Edge = instantiation. Multiple edges between nodes indicate multiple instantiations
 * Guaranteed to be acyclic by FIRRTL rules
 * @param circuit
 */
class ModuleInstanceGraph private(private val circuit: Circuit) extends Graph {
    private val moduleToId = mutable.HashMap[DefModule,NodeID]()
    private val idToModule = mutable.ArrayBuffer[DefModule]()
    private val moduleNameCache = mutable.HashMap[String,DefModule]()

    /**
     * Number of statements in this module only
     */
    private val idToStmtCount = mutable.HashMap[NodeID,Int]().withDefaultValue(0)

    // when object is constructed, go through circuit and create the graph
    visitModule(circuit.main)

    /**
     * Find the modules that are repeated
     */
    def getRepeatedModules(): collection.Set[DefModule] = (moduleToId filter {
        case (m:DefModule, id:NodeID) => inNeigh(id).size > 1
    }).keySet

    /**
     * Find largest common shared module.
     * For now, find the topmost repeated module
     * @return
     */
    def getGreatestCommonSharedModule: DefModule = {
        // TODO - allow for multiple of these. Need some heuristic then of what qualifies for dedup
        // find all repeated modules, then get the topmost one (fewest steps to the root)
        getRepeatedModules() map { x => nodeDepth(moduleToId(x)) } min
    }

    def utilGetDot(): String = {
        var ret = ""
        idToModule foreach { x => {
            val id = moduleToId(x)
            val tmp = if (inNeigh(id).size > 1) " color=blue" else ""
            ret += s"""  ${id} [label="${x.name}"${tmp}];  """
            }
        }

        (outNeigh zipWithIndex) foreach { case (outNeighs:mutable.ArrayBuffer[NodeID], id:NodeID) => {
            val first = /*idToModule(id).name*/ id + " -> "
            outNeighs foreach { ret += "\t" + first + _ + ";\n" }
        } }
        s"digraph test {\n${ret}\n}"
    }

    /**
     * Create node corresponding to module itself, then look thru each statement to find
     * any instantiations and create edges
     * @param m
     */
    private def visitModule(m: DefModule): Unit = {
        if (moduleToId contains m) {
            return
        } // already saw this one

        val modID = getID(m)
        m foreachStmt visitStmt(modID)
    }

    private def visitModule(modName: String): Unit = {
        visitModule(Extract.findModule(modName, circuit, moduleNameCache))
    }

    /**
     * Look thru each statement and create an edge if a module is instantiated
     * @param s
     */
    private def visitStmt(parentModuleID: NodeID)(s: Statement): Unit = s match {
        case b: Block => b.stmts foreach visitStmt(parentModuleID)
        case i: WDefInstance => {
            // Visit that module
            visitModule(i.module)

            // have the module name, need to get its ID
            val childID = getID(i.module)
            addEdge(parentModuleID, childID)
        }
        case _ => idToStmtCount(parentModuleID) += 1
    }

    private def getID(mod: DefModule): NodeID = {
        if (moduleToId contains mod) moduleToId(mod)
        else {
            val newID = moduleToId.size
            moduleToId(mod) = newID
            idToModule += mod
            growNeighsIfNeeded(newID)
            newID
        }
    }

    private def getID(modName: String): NodeID = {
        getID(Extract.findModule(modName, circuit, moduleNameCache))
    }
}

object ModuleInstanceGraph {
    def apply(circuit: Circuit): ModuleInstanceGraph = new ModuleInstanceGraph(circuit)
}