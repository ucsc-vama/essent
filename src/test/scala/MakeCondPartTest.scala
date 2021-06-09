package essent

import collection.mutable.ArrayBuffer
import org.scalatest._

import scala.language.postfixOps

class MakeCondPartTest extends FlatSpec {
  def makeStartingGraph(nModules: Int = 2): StatementGraph = {
    val sg = new StatementGraph

    def createSubModInstanceNodes(subName: String) = Seq(
      sg.addStatementNode(subName + ".a", Nil),
      sg.addStatementNode(subName + ".b", Nil),
      sg.addStatementNode(subName + ".c", Seq(subName + ".a", subName + ".b"))
    )

    val subs = 0 until nModules map(s"sub" + _) toList

    // create sub modules and set their tags
    for (subName <- subs; n <- createSubModInstanceNodes(subName)) {
      sg.idToTag(n) = subName + "."
    }

    // add connections between instances
    subs.sliding(2, 1).foreach({
      case left :: right :: Nil => sg.addEdge(s"$left.c", s"$right.a")
    })

    sg.addEdge("sub1.b", "sub2.b")

    sg
  }

  "a sample graph" should "work" in {
    val tmp = makeStartingGraph(4)
    val condPartWorker = MakeCondPart(tmp, new Renamer, Map.empty)
    val (ioForGcsm, compatiblePartitionings) = condPartWorker.findPartitionings()
    condPartWorker.doOpt(1)
    println(compatiblePartitionings)
  }
}
