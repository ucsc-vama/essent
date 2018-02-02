package essent

import collection.mutable.ArrayBuffer

object Util {
  // Given an array, returns a map of value to all indices that had that value (CAM-like)
  def groupIndicesByValue[T](a: ArrayBuffer[T]): Map[T, Seq[Int]] = {
    a.zipWithIndex.groupBy{ _._1 }.mapValues{ v => v.toSeq map { _._2 }}
  }

  // Given a list of pairs, returns a map of value of first element to all second values (CAM-like)
  def groupByFirst[T,Y](l: Seq[(T,Y)]): Map[T, Seq[Y]] = {
    l.groupBy{ _._1 }.mapValues{ v => v map { _._2 }}
  }
}
