package essent

import firrtl.ir.{Expression, Info, MultiInfo, NoInfo, Statement}

import collection.mutable.{ArrayBuffer, HashMap, ListBuffer}
import scala.collection.{GenTraversableOnce, IterableLike, MapLike, SetLike, immutable, mutable}
import scala.collection.generic.CanBuildFrom
import scala.reflect.ClassTag

object Util {
  /**
   * Given an array, returns a map of value to all indices that had that value (CAM-like)
   */
  def groupIndicesByValue[T](a: Iterable[T])(implicit tagT: ClassTag[T]): Map[T, Seq[Int]] = a.zipWithIndex.toMapOfLists[T, Int, Seq[Int]]

  def selectFromMap[K,V](selectors: Iterable[K], targetMap: collection.Map[K,V]): collection.Map[K,V] = {
    val selectorSet = selectors.toSet
    targetMap.filterKeys(selectorSet.contains)
  }

  def tidyString(str: String): String = {
    val charsToRemove = Set(' ', ',', '.', '(', ')')
    str filter { !charsToRemove.contains(_) }
  }

  def sortHashMapValues[K](hm: HashMap[K,Seq[Int]]) {
    hm.keys foreach { k => hm(k) = hm(k).sorted }
  }

  implicit class StringBuilderUtils(sb: StringBuilder) {
    /**
     * Append the given string and a newline
     * @param x the string
     * @return the StringBuilder, for chaining
     */
    def appendLine(x: String): StringBuilder = sb.append(x).append('\n')
  }

  /**
   * Utilities to add to the [[Iterable]]-derived classes, which is most of the list classes
   * @param iter
   * @tparam A
   */
  implicit class IterableUtils[+A](iter: Iterable[A]) {
    /**
     * Find the first occurence of the given item as an [[Option]]
     * @param item
     * @tparam B
     * @return
     */
    def getOption(item: Any): Option[A] = iter.find(item.equals(_))

    /**
     * Find the items which are equal in this collection
     * @param item
     * @return
     */
    def findEqual(item: Any): Iterable[A] = iter.filter(_.equals(item))

    /**
     * Given a list of pairs, returns a map of value of first element to all second values (CAM-like)
     * @tparam T key type
     * @tparam U value type
     * @tparam Ret The list type to return. Inferred from your calling context, and is probably [[IndexedSeq]] by default.
     */
    def toMapOfLists[T, U, Ret](implicit tagT: ClassTag[T], tagU: ClassTag[U], ev: A <:< (T, U), cbf: CanBuildFrom[Nothing, U, Ret]): Map[T, Ret] = {
      val b = mutable.Map[T, mutable.Builder[U, Ret]]()
      for ((k: T, v: U) <- iter) {
        b.getOrElseUpdate(k, cbf()) += v
      }
      b.mapValues(_.result).toMap // .toMap is important so that the `mapValues` gets expanded now and not later!
    }
  }

  implicit class MapUtils[K, +V](map: collection.Map[K, V]) {
    def intersect[B >: V](that: collection.Map[K, B]): Iterable[(K, V, B)] =
      for {
        key <- map.keys ++ that.keys
        if map.contains(key) && that.contains(key)
      } yield (key, map(key), that(key))

    def zipAllByKey[B >: V, C >: V](that: collection.Map[K, C], thisElem: B, thatElem: C): Iterable[(K, B, C)] =
      for (key <- map.keys ++ that.keys)
        yield (key, map.getOrElse(key, thisElem), that.getOrElse(key, thatElem))
  }

  implicit class StatementUtils(stmt: Statement) {
    /**
     * Same as foreachInfo on [[Statement]] except that this one recursively finds the [[Info]]s contained in [[MultiInfo]]
     */
    def foreachInfoRecursive(f: Info => Unit): Unit = {
      def foreachInfoRecursiveHelper(info: Info): Unit = info match {
        case MultiInfo(infos) => {
          f(info) // handle the MultiInfo itself, if desired
          infos foreach foreachInfoRecursiveHelper // recurse to handle the real infos
        }
        case _ => f(info) // this is a normal info object, handle it
      }

      stmt foreachInfo foreachInfoRecursiveHelper
    }

    /**
     * Filter the infos to find the ones matching the given type.
     * The first one matching will be returned
     */
    def getInfoByType[T <: Info]()(implicit tagT: ClassTag[T]): Option[T] = {
      var result: Option[T] = None
      stmt.foreachInfoRecursive {
        case i: T if result.isEmpty => result = Some(i)
        case _ =>
      }
      result
    }

    /**
     * Same as mapExpr on [[Statment]] except that this one recursively descends into the expressions contained in the tree
     */
    def mapExprRecursive(f: Expression => Expression): Statement = {
      def mapExprRecursiveHelper(expr: Expression): Expression = {
        f(expr).mapExpr(mapExprRecursiveHelper)
      }

      stmt mapExpr mapExprRecursiveHelper
    }
  }

  implicit class ExpressionUtils(expr: Expression) {
    /**
     * Similar to foreachExpr but also recurses through sub-expressions, calling their foreachExpr
     * @param f
     */
    def foreachExprRecursive(f: Expression => Unit): Unit = {
      def foreachExprRecursiveHelper(e: Expression): Unit = {
        f(e)
        e foreachExpr foreachExprRecursiveHelper
      }

      f(expr)
      expr foreachExpr foreachExprRecursiveHelper
    }

    /**
     * Filter the expressions to find the ones matching the given type.
     */
    def filterExprByType[T <: Expression]()(implicit tagT: ClassTag[T]): ListBuffer[T] = {
      val result = mutable.ListBuffer[T]()
      expr.foreachExprRecursive {
        case i: T => result += i
        case _ =>
      }
      result
    }
  }
}