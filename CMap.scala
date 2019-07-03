package distribution

import stainless.collection._
import stainless.lang._

case class CMap[A,B](f: A => B) {
  def apply(k: A): B = f(k)

  def updated(k: A, v: B) = CMap((x: A) => if (x == k) v else f(x))
}

object CMap {
  def apply[A,B](l: List[(A,B)], default: B): CMap[A,B] = {
    decreases(l.size)
    l match {
      case Nil() => CMap(_ => default)
      case Cons((a,b), ls) => CMap(ls, default).updated(a,b)
    }
  }

  def apply[A,B](default: B): CMap[A,B] = CMap(_ => default)
}
