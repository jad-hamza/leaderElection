package distribution

import leon.collection._
import leon.lang._

case class MMap[A,B](f: A => B) {

  
  def apply(k: A): B = {
    
    f(k)
     
  }
  
  def updated(k: A, v: B) = {
    MMap((x: A) => if (x == k) v else f(x))
  }
  
  def getOrElse(k: A, v: B) = {
    f(k)
  }

  def contains(k: A) = true
  
}

object MMap {

  def makeMapAux[A,B](l: List[(A, B)], f: A => B): MMap[A,B] = {
    l match {
      case Nil() => MMap(f)
      case Cons(x,xs) => makeMapAux(xs, (y: A) => if (y == x._1) x._2 else f(y))
    }
  }

  def makeMap[A,B](l: List[(A, B)]): MMap[A,B] = {
    require(!l.isEmpty)
    l match {
      case Cons(x,xs) => makeMapAux[A,B](xs, (y: A) => x._2)
    }
  }
    
}

