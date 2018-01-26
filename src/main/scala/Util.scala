package essent

import collection.mutable.ArrayBuffer

object Util {
  // Given an array, returns a map of value to all indices that had that value (CAM-like)
  def groupIndicesByValue[T](a: ArrayBuffer[T]): Map[T, Seq[Int]] = {
    a.zipWithIndex.groupBy{ _._1 }.mapValues{ v => v.toSeq map { _._2 }}
  }
}
