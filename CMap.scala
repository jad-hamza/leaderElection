package distribution

import leon.collection._
import leon.lang._

case class MMap[A,B](f: A => B) {

  
  def apply(k: A): B = {
    
    f(k).get
     
  }
  
  def updated(k: A, v: B) = {
    MMap((x: A) => if (x == k) v else f(x))
  }

}

object MMap {

  def makeMap[A,B](b: B): MMap[A,B] = MMap((x: A) => b)

}
