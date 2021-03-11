package essent

import org.scalatest.flatspec.AnyFlatSpec

class TopologicalSortSpec extends AnyFlatSpec {
  "Topological Sort" should "return a valid ordering" in {
    val bg = new Graph
    bg.addEdge(2,3)
    bg.addEdge(2,1)
    bg.addEdge(1,0)
    bg.addEdge(4,2)
    val topoSortResult = TopologicalSort(bg)
    assert(topoSortResult.lastIndexOf(2) < topoSortResult.lastIndexOf(3))
    assert(topoSortResult.lastIndexOf(2) < topoSortResult.lastIndexOf(1))
    assert(topoSortResult.lastIndexOf(1) < topoSortResult.lastIndexOf(0))
    assert(topoSortResult.lastIndexOf(4) < topoSortResult.lastIndexOf(2))
  }

  it should "detect a cycle" in {
    val bg = new Graph
    bg.addEdge(2,3)
    bg.addEdge(3,1)
    bg.addEdge(3,4)
    bg.addEdge(3,2)
    assertThrows[Exception]{ TopologicalSort(bg) }
  }
}
