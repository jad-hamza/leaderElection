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

  def makeMap[A,B](b: B): MMap[A,B] = MMap((x: A) => b)

}
