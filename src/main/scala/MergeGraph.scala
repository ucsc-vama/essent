package essent

import Graph.NodeID

import java.io.{File, FileWriter}
import collection.mutable.{ArrayBuffer, HashMap, HashSet}


// Fundamental assumptions:
//  * IDs match up with IDs in original Graph
//  * The mergeID is a member of the merged group and ID used
//  * MergeGraph will not add new nodes after built

class MergeGraph extends Graph {
  // node ID -> merge ID
  val idToMergeID = ArrayBuffer[NodeID]()

  // merge ID -> [member] node IDs (must include mergeID)
  val mergeIDToMembers = HashMap[NodeID, Seq[NodeID]]()

  // inherits outNeigh and inNeigh from Graph

  def buildFromGraph(g: Graph) {
    // FUTURE: cleaner way to do this with clone on superclass?
    outNeigh.appendAll(ArrayBuffer.fill(g.numNodes)(ArrayBuffer[NodeID]()))
    inNeigh.appendAll(ArrayBuffer.fill(g.numNodes)(ArrayBuffer[NodeID]()))
    g.nodeRange foreach { id => {
      g.outNeigh(id).copyToBuffer(outNeigh(id))
      g.inNeigh(id).copyToBuffer(inNeigh(id))
    }}
    ArrayBuffer.range(0, numNodes()).copyToBuffer(idToMergeID)
    nodeRange() foreach { id  => mergeIDToMembers(id) = Seq(id) }
  }

  def applyInitialAssignments(initialAssignments: ArrayBuffer[NodeID]) {
    // FUTURE: support negative (unassigned) initial assignments
    idToMergeID.clear()
    mergeIDToMembers.clear()
    initialAssignments.copyToBuffer(idToMergeID)
    val asMap = Util.groupIndicesByValue(initialAssignments)
    asMap foreach { case (mergeID, members) => {
      assert(members.contains(mergeID))
      mergeIDToMembers(mergeID) = members
      mergeNodesMutably(mergeID, members diff Seq(mergeID))
    }}
  }

  def mergeGroups(mergeDest: NodeID, mergeSources: Seq[NodeID]) {
    val newMembers = (mergeSources map mergeIDToMembers).flatten
    newMembers foreach { id => idToMergeID(id) = mergeDest}
    mergeIDToMembers(mergeDest) ++= newMembers
    mergeSources foreach { id => mergeIDToMembers.remove(id) }
    mergeNodesMutably(mergeDest, mergeSources)
  }

  def nodeSize(n: NodeID) = mergeIDToMembers.getOrElse(n,Seq()).size

  def iterGroups() = mergeIDToMembers

  def paint(fileName: String) = {
    val dotWriter = new FileWriter(new File("./", fileName))

    def writeLine(indentLevel: Int, line: String) {
      dotWriter write ("  "*indentLevel + line + "\n")
    }

    val maxsubNodes = (mergeIDToMembers.values map{case s: Seq[NodeID] => s.size}).max

    writeLine(0, "digraph MergeGraph {")

    for (eachNode <- mergeIDToMembers.keys) {
      val nodeLabel = eachNode
      writeLine(1, s"""n$eachNode [label=\"$nodeLabel\"];""")
    }

    val merge_inNeigh = ArrayBuffer.fill(inNeigh.size)(ArrayBuffer[NodeID]())

    for (dst_mergeID <- mergeIDToMembers.keys) {
      for (each_dst_id <- mergeIDToMembers(dst_mergeID)) {
        for (each_src_id <- inNeigh(each_dst_id)) {
          val src_mergeID = idToMergeID(each_src_id)
          merge_inNeigh(dst_mergeID).append(src_mergeID)
        }
      }
    }


    // Note: MergeIDs are subset of ID (not continuous)


//    val merge_inNeigh_distinct = merge_inNeigh.map{in: ArrayBuffer[NodeID] => in.distinct}

    for (eachNode <- mergeIDToMembers.keys) {
      for (eachSrcNode <- merge_inNeigh(eachNode).distinct) {
        writeLine(1, s"n$eachSrcNode -> n$eachNode;")
      }
    }

    writeLine(0, "}")

    dotWriter.close()
  }
}


object MergeGraph {
  def apply(g: Graph): MergeGraph = {
    val mg = new MergeGraph
    mg.buildFromGraph(g)
    mg
  }

  def apply(g: Graph, initialAssignments: ArrayBuffer[NodeID]): MergeGraph = {
    // TODO: remove unecessary building if using initialAssignments
    val mg = apply(g)
    mg.applyInitialAssignments(initialAssignments)
    mg
  }
}
