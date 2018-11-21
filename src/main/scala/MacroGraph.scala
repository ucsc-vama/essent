package essent

import collection.mutable.{ArrayBuffer, HashMap}

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
    externalDestMacroIDs.copyToBuffer(outNeigh(macroID))
    val allInSources = memberSet flatMap fg.inNeigh
    val externalSources = allInSources -- memberSet
    val externalSourceMacroIDs = externalSources map idToMacroID filter { _ >= 0 }
    externalSourceMacroIDs.copyToBuffer(inNeigh(macroID))
  }

  // NOTE: overwrites prior memberships
  def createMacro(newMacroID: Int, newMembers: Seq[Int]) {
    val origMacroIDs = (newMembers map idToMacroID filter { _ >= 0 }).distinct
    newMembers foreach { idToMacroID(_) = newMacroID }
    origMacroIDs foreach {
      macroID => members(macroID) = members(macroID) diff newMembers
    }
    (origMacroIDs ++ Seq(newMacroID)) foreach recomputeMacroEdges
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
}

// TODO: how do you assign IDs and prevent graph from giving wrong ones?
// FUTURE: pull string names out of graph?

object MacroGraph {
  // TODO: set convention that macroID < 0 means don't map?
  def apply(fg: Graph, initialAssignments: ArrayBuffer[Int]): MacroGraph = {
    val mg = new MacroGraph(fg)
    initialAssignments.copyToBuffer(mg.idToMacroID)
    val asMap = Util.groupIndicesByValue(initialAssignments)
    val dropNegIDs = asMap filter { case (key, value) => key >= 0 }
    dropNegIDs foreach { case (key,value) => mg.members(key) = value }
    mg.members.keys foreach mg.recomputeMacroEdges
    mg
  }
}