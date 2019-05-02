package distribution

import stainless.collection._
import stainless.lang._

case class Map[A,B](f: A => Option[B]) {

  def contains(k: A): Boolean = f(k) != None[B]()


  def apply(k: A): B = {
    require(contains(k))

    f(k).get

  }

  def updated(k: A, v: B) = {
    Map((x: A) => if (x == k) Some(v) else f(x))
  }

  def getOrElse(k: A, v: B) = {
    if (contains(k)) f(k).get
    else v
  }
}

object Map {

  def apply[A,B](): Map[A,B] = Map((x: A) => None[B]())

}
