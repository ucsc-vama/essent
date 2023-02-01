package essent

import collection.mutable.{ArrayBuffer, HashMap}
import java.io.Writer


object Util {
  // Given an array, returns a map of value to all indices that had that value (CAM-like)
  def groupIndicesByValue[T](a: ArrayBuffer[T]): Map[T, Seq[Int]] = {
    a.zipWithIndex.groupBy{ _._1 }.mapValues{ v => v.toSeq map { _._2 }}
  }

  // Given a list of pairs, returns a map of value of first element to all second values (CAM-like)
  def groupByFirst[T,Y](l: Seq[(T,Y)]): Map[T, Seq[Y]] = {
    l.groupBy{ _._1 }.mapValues{ v => v map { _._2 }}
  }

  def selectFromMap[K,V](selectors: Seq[K], targetMap: Map[K,V]): Map[K,V] = {
    (selectors flatMap {
      k => if (targetMap.contains(k)) Seq(k -> targetMap(k)) else Seq()
    }).toMap
  }

  def tidyString(str: String): String = {
    val charsToRemove = Set(' ', ',', '.', '(', ')')
    str filter { !charsToRemove.contains(_) }
  }

  def sortHashMapValues[K](hm: HashMap[K,Seq[Int]]) {
    hm.keys foreach { k => hm(k) = hm(k).sorted }
  }

  // Extends the Writer to have the writeLines method below to indent and auto-terminate strings
  implicit class IndentWriter(writer: Writer) {
    val indent = "  "

    def writeLines(indentLevel: Int, lines: String): Unit = {
      writeLines(indentLevel, Seq(lines))
    }

    def writeLines(indentLevel: Int, lines: Seq[String]): Unit = {
      lines foreach { s => writer.write(indent * indentLevel + s + "\n") }
    }
  }
}
