package essent

import essent.Extract._
import essent.Graph.NodeID
import firrtl.ir._
import essent.ir._
import essent.Util.removeDots

import collection.mutable.HashMap

trait SigDecType
case object ExtIO extends SigDecType
case object RegSet extends SigDecType
case object Local extends SigDecType
case object MuxOut extends SigDecType
case object PartOut extends SigDecType
case object PartCache extends SigDecType

case class SigMeta(decType: SigDecType, sigType: firrtl.ir.Type)

class Renamer {
  val nameToEmitName = HashMap[String,String]()
  val nameToMeta = HashMap[String,SigMeta]()

  // Outside datastructure, contains memory and registers in outside
  val outsideDSName = "circuitState"
  // Name used to access dedup data from outside
  def getDedupInstanceDSName(idx: Int) = s"dedupInst_${idx}"
  // Name used to access dedup data from inside. This should be same with EssentEmitter.dedupCitcuitDSInstName
  val dedupCitcuitDSInstName = "dedupData"

  def populateFromSG(sg: StatementGraph, extIOMap: Map[String,Type]) {
    val stateNames = sg.stateElemNames.toSet
    sg.nodeRange foreach { id => {
      val name = sg.idToName(id)
      val decType = if (stateNames.contains(name))        RegSet
                    else if (extIOMap.contains(name))     ExtIO
                    else                                  Local
      val sigType = if (extIOMap.contains(name)) extIOMap(name)
                    else findResultType(sg.idToStmt(id))
      nameToEmitName(name) = name
      nameToMeta(name) = SigMeta(decType, sigType)
    }}
    val unusedExtSigs = extIOMap.keys.toSet -- sg.nameToID.keys
    unusedExtSigs foreach { name => {
      nameToEmitName(name) = name
      nameToMeta(name) = SigMeta(ExtIO, extIOMap(name))
    }}
    fixEmitNames()
  }

  def fixEmitNames() {
    def shouldBeLocal(meta: SigMeta) = meta.decType match {
      case Local | MuxOut | PartOut => true
      case _ => false
    }
    val namesToLocalize = nameToMeta collect {
      case (name, meta) if (shouldBeLocal(meta)) => name
    }
    namesToLocalize foreach {
      name => nameToEmitName(name) = removeDots(nameToEmitName(name))
    }
  }

  def mutateDecTypeIfLocal(name: String, newDecType: SigDecType) {
    val currentMeta = nameToMeta(name)
    if (currentMeta.decType == Local)
      nameToMeta(name) = currentMeta.copy(decType = newDecType)
  }

  def addPartCache(name: String, sigType: firrtl.ir.Type) {
    nameToEmitName(name) = removeDots(name)
    nameToMeta(name) = SigMeta(PartCache, sigType)
  }

  def doNotDecLocal() = {
    val notLocalSigs = nameToMeta collect {
      case (name, SigMeta(decType, sigType)) if (decType != Local) => name
    }
    notLocalSigs.toSet
  }


  def factorFlatternedMemoryName(dedupCPInfo: DedupCPInfo) = {
    // factor all memory access
    dedupCPInfo.allMemoryNames.foreach{canonicalName => {
      val declName = removeDots(canonicalName)
      val fullName = s"${outsideDSName}.${declName}"
      nameToEmitName(canonicalName) = fullName
    }}
  }

  def factorExtModuleName(dedupCPInfo: DedupCPInfo): Unit = {
    // For each ExtIO
    nameToMeta.filter{case (_, SigMeta(declType, _)) => {declType == ExtIO}}.foreach{case (name, SigMeta(declType, signalType)) => {
      val splitByDots = name.split('.')
      val signalName = splitByDots.last
      val hierarchyName = splitByDots.dropRight(1).mkString(".")
      val instName = removeDots(hierarchyName)
      // Note: Patch for topModule. TopModule signals are marked as ExtIO
      val fullName = if (instName.nonEmpty) s"${instName}.${signalName}" else signalName

      nameToEmitName(name) = fullName
    }}
  }

  def factorNameForDedupCircuit(sg: StatementGraph, dedupCPInfo: DedupCPInfo): Unit = {
    factorFlatternedMemoryName(dedupCPInfo)
    factorExtModuleName(dedupCPInfo)

    // factor all register access
    // In original design, registers are accessed using canonical name

    // Dedup instance registers.
    // Note: For dedup instance registers, only need to rename for main instance
    // As only main instance would go to code gen
    dedupCPInfo.dedupRegisterNamesByInst.foreach{ case (instName, registerNames) => {
      if (instName == dedupCPInfo.dedupMainInstanceName) {
        registerNames.foreach{rname => {
          val shortName = rname.stripPrefix(instName)
          val declName = removeDots(shortName)
          val fullName = s"(${dedupCitcuitDSInstName}->${declName})"
          nameToEmitName(rname) = fullName
        }}
      } else {
        // Remove unused signal
        registerNames.foreach{rname => {
          nameToEmitName(rname) = "!!ShouldntReachHere!!"
        }}
      }
    }}

    dedupCPInfo.allRegisterNames.foreach {canonicalName => {

      if (!dedupCPInfo.dedupRegisterNames.contains(canonicalName)) {
        // Outside circuit registers
        // Assertion: Those registers are not renamed yet
//        assert(nameToEmitName(canonicalName) == canonicalName)
        if (nameToEmitName(canonicalName) != canonicalName) {
          println(canonicalName)
          println(nameToEmitName(canonicalName))
          assert(false)
        }

        val declName = removeDots(canonicalName)
        nameToEmitName(canonicalName) = s"${outsideDSName}.${declName}"
      }
    }}

    // rename partcache
    // For main instance
    dedupCPInfo.mainDedupInstInternalSignals.foreach{sigName =>
      val declName = removeDots(sigName.stripPrefix(dedupCPInfo.dedupMainInstanceName))
      nameToEmitName(sigName) = s"(${dedupCitcuitDSInstName}->${declName})"
    }
    dedupCPInfo.mainDedupInstBoundarySignals.diff(dedupCPInfo.allRegisterNames).diff(dedupCPInfo.allMemoryNames).foreach{ sigName =>
      val declName = removeDots(sigName.stripPrefix(dedupCPInfo.dedupMainInstanceName))
      nameToEmitName(sigName) = s"(${dedupCitcuitDSInstName}->${declName})"
    }

  }

  def factorNameForOutsideCircuit(sg: StatementGraph, dedupCPInfo: DedupCPInfo): Unit = {
    factorFlatternedMemoryName(dedupCPInfo)
    factorExtModuleName(dedupCPInfo)


    // factor all register access
    // In original design, registers are accessed using canonical name

    // Dedup instance registers.
    // Note: For outside circuit, every instance need to be renamed
    dedupCPInfo.dedupRegisterNamesByInst.foreach{ case (instName, registerNames) => {
      val instId = dedupCPInfo.dedupInstanceNameToId(instName)
      registerNames.foreach{rname => {
        val shortName = rname.stripPrefix(instName)
        val declName = removeDots(shortName)
        val fullName = s"(${getDedupInstanceDSName(instId)}.${declName})"
        nameToEmitName(rname) = fullName
      }}
    }}

    // Any register outside
    dedupCPInfo.allRegisterNames.foreach {canonicalName => {
      if (!dedupCPInfo.dedupRegisterNames.contains(canonicalName)) {
        // Outside circuit registers
        // Assertion: Those registers are not renamed yet
        assert(nameToEmitName(canonicalName) == canonicalName)

        val declName = removeDots(canonicalName)
        nameToEmitName(canonicalName) = s"${outsideDSName}.${declName}"
      }
    }}

    // rename partcache
    // For main instance
    dedupCPInfo.allDedupInstInternalSignals.foreach{sigName => {
      // Outside circuit should not touch dedup internal signals
      nameToEmitName(sigName) = "!!!Should_not_access_this_signal!!!"
    }}

    dedupCPInfo.allDedupInstBoundarySignals.foreach{sigName => {
      if (dedupCPInfo.signalWriteOnlyByOutside(sigName)) {
        // Don't rename if already renamed (signals can be registers or memories)
        if (nameToEmitName(sigName) == sigName) {
          val declName = removeDots(sigName)
          nameToEmitName(sigName) = s"${outsideDSName}.${declName}"
        }

      } else {
        val signalReaderCPids = dedupCPInfo.inputSignalNameToCPid.getOrElse(sigName, Set[NodeID]())
        val signalWriterCPids = dedupCPInfo.outputSignalNameToCPid.getOrElse(sigName, Set[NodeID]())
        val signalCPId_ = signalWriterCPids ++ signalReaderCPids

        val instName_ = signalCPId_.filter(dedupCPInfo.allDedupCPids).map(dedupCPInfo.cpIdToDedupInstName)
        assert(instName_.size == 1)
        val instName = instName_.head
        val instId = dedupCPInfo.dedupInstanceNameToId(instName)

        val declName = removeDots(sigName.stripPrefix(instName))
        assert(declName != "tile_reset_domain$tile$dcache$doUncachedResp")
        assert(nameToEmitName(sigName) != sigName)
        nameToEmitName(sigName) = s"(${getDedupInstanceDSName(instId)}.${declName})"
      }

    }}


  }

  def decLocal(name: String) = nameToMeta(name).decType == Local

  def emit(canonicalName: String): String = nameToEmitName(canonicalName)
  
  def vcdOldValue(sig_name: String) = sig_name + "_old" 
}

object Renamer {
  def apply(rn: Renamer) = {
    val new_rn = new Renamer
    new_rn.nameToEmitName ++= rn.nameToEmitName
    new_rn.nameToMeta ++= rn.nameToMeta
    new_rn
  }
}
// object Renamer {
//   def apply(ng: NamedGraph, extIOMap: Map[String,Type]) = {
//     val rn = new Renamer
//     rn.populateFromNG(ng, extIOMap)
//     rn
//   }
// }
