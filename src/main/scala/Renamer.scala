package essent

import essent.Extract._
import essent.ir.GCSMSignalPlaceholder
import firrtl.WRef
import firrtl.ir._

import collection.mutable.HashMap
import scala.collection.mutable

sealed trait SigDecType
case object ExtIO extends SigDecType
case object RegSet extends SigDecType
case object Local extends SigDecType
case object MuxOut extends SigDecType
case object PartOut extends SigDecType
case object PartCache extends SigDecType
case object GCSMSignal extends SigDecType

sealed case class SigMeta(decType: SigDecType, sigType: firrtl.ir.Type)

class Renamer {
  val nameToEmitName: mutable.Map[String, String] = HashMap[String,String]()
  val nameToMeta: mutable.Map[String, SigMeta] = HashMap[String,SigMeta]()

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

  def addGcsmSignals(gcsrs: Iterable[GCSMSignalPlaceholder]) = {
    gcsrs foreach { gcsr =>
      nameToEmitName(gcsr.name) = removeDots(Emitter.emitExpr(gcsr)(this))
      nameToMeta(gcsr.name) = SigMeta(GCSMSignal, gcsr.tpe)
    }
  }

  def removeDots(s: String) = s.replace('.','$')

  // TODO - clean up these methods
  def decLocal(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == Local

  def decExtIO(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == ExtIO

  def decRegSet(name: String): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == RegSet

  def isDec(name: String, decType: SigDecType): Boolean = nameToMeta.contains(name) && nameToMeta(name).decType == decType

  def emit(canonicalName: String): String = nameToEmitName(canonicalName)

  def getSigType(name: String): firrtl.ir.Type = nameToMeta(name).sigType
}

/**
 * Same as Renamer, but with overrideable signals. This allows
 * Used for the GCSM signals.
 */
class OverridableRenamer(orig: Renamer) extends Renamer {
  override val nameToEmitName = new OverridableMap[String, String](orig.nameToEmitName)
  override val nameToMeta = new OverridableMap[String, SigMeta](orig.nameToMeta)
}

/**
 * Map class which holds a reference to another map, as well as allowing for modifications that
 * don't affect the original. Only supports updates and additions
 * @param orig the backing map. it isn't modified by this class, but could be modified by someone else
 */
sealed class OverridableMap[K, V](orig: collection.Map[K, V]) extends mutable.Map[K, V] {
  /**
   * Only stores the new values
   */
  private val overrides = new HashMap[K, V]()

  override def +=(kv: (K, V)): OverridableMap.this.type = {
    overrides += kv
    this
  }
  override def -=(key: K): OverridableMap.this.type = throw new NotImplementedError
  override def get(key: K): Option[V] = overrides.get(key).orElse(orig.get(key))
  override def iterator: Iterator[(K, V)] = new Iterator[(K, V)] {
    private val keysIter = (overrides.keySet ++ orig.keySet).toIterator
    override def hasNext: Boolean = keysIter.hasNext
    override def next(): (K, V) = {
      val k = keysIter.next()
      (k, OverridableMap.this.apply(k))
    }
  }
}
