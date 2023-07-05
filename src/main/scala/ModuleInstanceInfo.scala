package essent

import firrtl.ir._
import essent.Emitter._
import essent.Extract._
import essent.ir._
import _root_.logger.LazyLogging
import firrtl.AnnotationSeq

import collection.mutable.{ArrayBuffer, BitSet, HashMap}

class ModuleInstanceInfo(circuit: Circuit, annotations: AnnotationSeq, sg:StatementGraph) extends LazyLogging{

  val moduleDedupTable = findModuleDedupTable(annotations)

  // Module name and corresponding instance name
  val modInsts = findAllModuleInstances(circuit)
  val extModInsts = findExtModuleInstances(modInsts, circuit)

  // Module names for all, extmodule and internal module
  val allModNames = modInsts.map(_._1).distinct
  val extModNames = extModInsts.map(_._1).distinct
  val internalModNames = allModNames.filterNot(extModNames.contains)

  // Module name -> instances map
  val allModInstanceTable = modInsts.groupBy(_._1).map{case(modName, insts) => modName -> insts.map(_._2)}
  val extModInstanceTable = allModInstanceTable.filter{case (modName, _) => extModNames.contains(modName)}
  val internalModInstanceTable = allModInstanceTable.filterNot{case (modName, _) => extModNames.contains(modName)}

  // List of instances
  val allInstNames = modInsts.map(_._2)
  val extInstNames = extModInsts.map(_._2)
  val internalInstNames = internalModNames.flatMap(allModInstanceTable)


  // DEBUG: Correctness check. FIRRTL dedup result should also available directly from circuit.
  //       This code is used to check correctness of FIRRTL dedup.
  moduleDedupTable.foreach{case (modFrom, modTo) => {
    assert(allModNames.contains(modTo))
    if (modFrom != modTo) {
      // Duplicate modules
      assert(!allModNames.contains(modFrom))
    }
  }}

  // Instance size table (in number of IR nodes)
  val (instExclusiveNodesTable, instInclusiveNodesTable) = extractInstanceNodesTable(sg, internalInstNames)

  // DEBUG: Ensure instances of a same module has same amount of nodes
  internalModInstanceTable.foreach{case (modName, insts) => {
    val firstInstanceSize = instInclusiveNodesTable(insts.head).length
    insts.foreach{instName => {
      assert(instInclusiveNodesTable(instName).length == firstInstanceSize)
    }}
  }}

  // Find module size (include sub-modules) for every internal module.
  // Simply pick the size of first instance. Every instance of same module should have same size
  val internalModIRSize = internalModInstanceTable.map{case (modName, insts) => {
    modName -> (instInclusiveNodesTable(insts.head).length)
  }}
}
