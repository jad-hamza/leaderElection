package distribution

import leon.collection._
import leon.lang._

case class MMap[A,B](m: Map[A, B]) {
  
  def apply(k: A): B = {
    require (m.contains(k))
      m.apply(k)
  }
  
  def updated(k: A, v: B) = {
    MMap(m.updated(k, v))
  }
  
  def getOrElse(k: A, v: B) = {
    m.getOrElse(k, v)
  }

  def contains(k: A) = {
    m.contains(k)
  }
  
}

object MMap {
  def makeMapAux[A,B](l: List[(A, B)], m: Map[A,B]): MMap[A,B] = {
    l match {
      case Nil() => MMap(m)
      case Cons(x,xs) => makeMapAux(xs, (m + x))
    } 
  }
  
  def makeMap[A,B](l: List[(A, B)]): MMap[A,B] = {
    makeMapAux[A,B](l, Map[A,B]())
  }
}
