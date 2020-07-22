package disabled

import essent.Util

import collection.mutable.{ArrayBuffer, HashMap, HashSet}

// NOTE: macro IDs are for within this class, node IDs are for companion graph
class MacroGraph(fg: Graph) extends Graph {
  // node ID -> macro ID
  val idToMacroID = ArrayBuffer[Int]()

  // macro ID -> [member] node IDs
  val members = HashMap[Int, Seq[Int]]()

  // Inherit outNeigh and inNeigh from Graph

  def recomputeMacroEdges(macroID: Int) {
    val memberSet = members(macroID).toSet
    val allOutDests = memberSet flatMap fg.outNeigh
    val externalDests = allOutDests -- memberSet
    val externalDestMacroIDs = externalDests map idToMacroID filter { _ >= 0 }
    outNeigh(macroID).clear()
    externalDestMacroIDs.copyToBuffer(outNeigh(macroID))
    val allInSources = memberSet flatMap fg.inNeigh
    val externalSources = allInSources -- memberSet
    val externalSourceMacroIDs = externalSources map idToMacroID filter { _ >= 0 }
    inNeigh(macroID).clear
    externalSourceMacroIDs.copyToBuffer(inNeigh(macroID))
  }

  // NOTE: overwrites prior memberships
  def createMacro(newMacroID: Int, newMembers: Seq[Int]) {
    val origMacroIDs = newMembers map idToMacroID
    val origOutMacroIDs = newMembers flatMap fg.outNeigh map idToMacroID
    val origInMacroIDs = newMembers flatMap fg.inNeigh map idToMacroID
    val macroIDsToUpdate = (origMacroIDs ++ origOutMacroIDs ++ origInMacroIDs).distinct filter { _ >= 0 }
    newMembers foreach { idToMacroID(_) = newMacroID }
    origMacroIDs foreach {
      macroID => members(macroID) = members(macroID) diff newMembers
    }
    members(newMacroID) = newMembers
    (macroIDsToUpdate :+ newMacroID) foreach recomputeMacroEdges
  }

  def findMemberIDsForIncomingMacro(sourceMacroID: Int, destMacroID: Int): Seq[Int] = {
    members(destMacroID) filter {
      nodeID => fg.inNeigh(nodeID) map idToMacroID contains sourceMacroID
    }
  }
  def findMemberIDsForOutgoingMacro(sourceMacroID: Int, destMacroID: Int): Seq[Int] = {
    members(sourceMacroID) filter {
      nodeID => fg.outNeigh(nodeID) map idToMacroID contains destMacroID
    }
  }

  def createNewMacroID(): Int = {
    val newMacroID = members.keys.max + 1
    outNeigh += ArrayBuffer[Int]()
    inNeigh += ArrayBuffer[Int]()
    validNodes += newMacroID
    nameToID += (s"m-$newMacroID" -> newMacroID)
    members(newMacroID) = Seq()
    newMacroID
  }

  def checkMacrosDisjoint(): Boolean = {
    val includedSoFar = HashSet[Int]()
    members forall { case (macroID, memberIDs) => {
      val overlap = includedSoFar.intersect(memberIDs.toSet).nonEmpty
      includedSoFar ++= memberIDs
      !overlap
    }}
  }
}

// TODO: how do you assign IDs and prevent graph from giving wrong ones?

object MacroGraph {
  // TODO: set convention that macroID < 0 means don't map?
  def apply(fg: Graph, initialAssignments: ArrayBuffer[Int]): MacroGraph = {
    val mg = new MacroGraph(fg)
    initialAssignments.copyToBuffer(mg.idToMacroID)
    val asMap = Util.groupIndicesByValue(initialAssignments)
    val dropNegIDs = asMap filter { case (key, value) => key >= 0 }
    dropNegIDs foreach { case (key,value) => mg.members(key) = value }
    val largestMacroID = initialAssignments.max
    mg.outNeigh ++= ArrayBuffer.fill(largestMacroID+1)(ArrayBuffer[Int]())
    mg.inNeigh ++= ArrayBuffer.fill(largestMacroID+1)(ArrayBuffer[Int]())
    mg.members.keys foreach mg.recomputeMacroEdges
    // FUTURE: pull string names out of graph?
    mg.validNodes ++= mg.members.keys
    mg.nameToID ++= mg.members.keys map { macroID => (s"m-$macroID" -> macroID) }
    mg
  }
}