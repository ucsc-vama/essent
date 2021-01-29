package essent

import essent.Extract._
import firrtl.WRef
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

  def removeDots(s: String) = s.replace('.','$')

  // TODO - clean up these methods
  def decLocal(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == Local
  def decLocal(w: WRef): Boolean = decLocal(w.name)

  def decExtIO(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == ExtIO
  def decExtIO(w: WRef): Boolean = decExtIO(w.name)

  def decRegSet(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == RegSet
  def decRegSet(w: WRef):  Boolean = decRegSet(w.name)

  def isDec(name: String, decType: SigDecType): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == decType
  def isDec(w: WRef, decType: SigDecType): Boolean = isDec(w.name, decType)

  def emit(canonicalName: String): String = nameToEmitName(canonicalName)
}

// object Renamer {
//   def apply(ng: NamedGraph, extIOMap: Map[String,Type]) = {
//     val rn = new Renamer
//     rn.populateFromNG(ng, extIOMap)
//     rn
//   }
// }
