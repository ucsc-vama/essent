package essent

import essent.Extract._

import firrtl.ir._

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

  def populateFromSG(sg: StatementGraph, extIOMap: Map[String,Type], isParallel: Boolean = false) {
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
    fixEmitNames(isParallel)
  }

  def fixEmitNames(isParallel: Boolean) {
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

    if (isParallel) {
      def shouldBeGlobal(meta: SigMeta) = meta.decType match {
        case RegSet => true
        case _ => false
      }

      val namesToGlobalize = nameToMeta collect {
        case (name, meta) if (shouldBeGlobal(meta)) => name
      }
      namesToGlobalize foreach {
        name => nameToEmitName(name) = decGlobalize(nameToEmitName(name))
      }

      def shouldBeExtIO(meta: SigMeta) = meta.decType match {
        case ExtIO => true
        case _ => false
      }

      val extIOs = nameToMeta collect {
        case (name, meta) if (shouldBeExtIO(meta)) => name
      }

      extIOs foreach {
        name => nameToEmitName(name) = extIOGlobalize(name)
      }
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

  def decGlobalize(s: String) = "dat." + s.replace('.', '_')

  // Assumption: ExtModules are only 1 level depth
  def extIOGlobalize(s: String) = {

    val tokens = s.split('.')
    if (tokens.length == 1) {
      tokens.last
    } else {
      tokens.slice(0, tokens.length - 1).mkString("_") + "." + tokens.last
    }
  }

  def removeDots(s: String) = s.replace('.','$')

  def decLocal(name: String) = nameToMeta(name).decType == Local

  def emit(canonicalName: String): String = nameToEmitName(canonicalName)
}

// object Renamer {
//   def apply(ng: NamedGraph, extIOMap: Map[String,Type]) = {
//     val rn = new Renamer
//     rn.populateFromNG(ng, extIOMap)
//     rn
//   }
// }
