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

case class SigMeta(decType: SigDecType, sigType: firrtl.ir.Type)

class Renamer {
  val nameToEmitName = HashMap[String,String]()
  val nameToMeta = HashMap[String,SigMeta]()

  def populateFromNG(ng: NamedGraph, extIOMap: Map[String,Type]) {
    val stateNames = ng.stateElemNames.toSet
    ng.nodeRange foreach { id => {
      val name = ng.idToName(id)
      val decType = if (stateNames.contains(name))        RegSet
                    else if (extIOMap.contains(name))     ExtIO
                    else                                  Local
      val sigType = if (extIOMap.contains(name)) extIOMap(name)
                    else findResultType(ng.idToStmt(id))
      nameToEmitName(name) = name
      nameToMeta(name) = SigMeta(decType, sigType)
    }}
    val unusedExtSigs = extIOMap.keys.toSet -- ng.nameToID.keys
    unusedExtSigs foreach { name => {
      nameToEmitName(name) = name
      nameToMeta(name) = SigMeta(ExtIO, extIOMap(name))
    }}
  }

  def mutateDecTypeIfLocal(name: String, newDecType: SigDecType) {
    val currentMeta = nameToMeta(name)
    if (currentMeta.decType == Local)
      nameToMeta(name) = currentMeta.copy(decType = newDecType)
  }

  def doNotDecLocal() = {
    val notLocalSigs = nameToMeta collect {
      case (name, SigMeta(decType, sigType)) if (decType != Local) => name
    }
    notLocalSigs.toSet
  }

  def decLocal(name: String) = nameToMeta(name).decType == Local
}

// object Renamer {
//   def apply(ng: NamedGraph, extIOMap: Map[String,Type]) = {
//     val rn = new Renamer
//     rn.populateFromNG(ng, extIOMap)
//     rn
//   }
// }
