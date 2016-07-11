package distribution


import FifoNetwork._
import Networking._
import Protocol._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof3 {
  import Protocol._
  import PrettyPrinting._
  import ProtocolProof._
  import ProtocolProof2._
  
  
// property 10
// less than two WW
  def prop10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        prop10One(messages.getOrElse(x, Nil())) &&
        prop10(messages, xs)
    }
  }
  
  def prop10One(
    list: List[Message]
  ): Boolean = {
    list match {
      case Nil() => true
      case Cons(x@WriteWaiting(s,i,id,h), xs) => 
        !collectWWs(xs).contains(WriteUser(s,i)) &&
        prop10One(xs)
      case Cons(x,xs) => 
        prop10One(xs)
    }
  }
  
  def removeWSprop10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      prop10(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteSystem(s,i,idM,h), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    val WriteSystem(s,i,_,_) = m
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        theoremWS(messages.getOrElse(c, Nil()), m) &&
        collectWSs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i)) &&
        !collectWWs(newMessages.getOrElse((x._2,x._2), Nil())).contains(WriteUser(s,i))
      case Cons(x,xs) =>
        removeWSprop10(messages, xs, c) &&
        !collectWWs(newMessages.getOrElse((c._2,c._2), Nil())).contains(WriteUser(s,i))
    }
  }holds

  def removeWWprop10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop10(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteWaiting(s,i,idM,h), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    val WriteWaiting(s,i,_,_) = m
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) =>
        !collectWWs(newChan).contains(WriteUser(s,i)) &&
        prop10One(newChan) &&
        newMessages.getOrElse(c, Nil()) == newChan &&
        true
      case Cons(x,xs) => 
        removeWWprop10(messages, xs, c) &&
        !collectWWs(newMessages.getOrElse(c, Nil())).contains(WriteUser(s,i))
    }
    
  }holds
  
  def removeAllprop10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop10(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) =>
        newMessages.getOrElse(x, Nil()) == newChan &&
        prop10One(newChan) &&
        removeAllprop10(messages, xs, c) &&
        prop10(newMessages, channels)
      case Cons(x,xs) => 
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        prop10One(newMessages.getOrElse(x, Nil())) &&
        removeAllprop10(messages, xs, c) &&
        prop10(newMessages, channels)
    }
    
  }holds
  
  def removeProp10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      prop10(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    
    m match {
      case WriteSystem(s,i,_,_) =>
        removeWSprop10(messages, channels, c) &&
        removeAllprop10(messages, channels, c) &&
        prop10(newMessages, channels) &&
        !collectWWs(messages.getOrElse((c._2,c._2), Nil())).contains(WriteUser(s,i))
        true
      case WriteWaiting(s,i,_,_) => 
        removeWWprop10(messages, channels, c) &&
        removeAllprop10(messages, channels, c) &&
        prop10(newMessages, channels) &&
        !collectWWs(newMessages.getOrElse(c, Nil())).contains(WriteUser(s,i))
      case _ => 
        removeAllprop10(messages, channels, c) &&
        prop10(newMessages, channels)
    }
   
  }holds 
  
  def addWWProp10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      {
        m match {
          case WriteWaiting(s,i,_,_) => 
            !collectWWs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i))
          case _ => false
        }
      } &&
      prop10(messages, channels)
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x, xs) if (x == c) =>
        addWWProp10One(messages.getOrElse(x, Nil()), m) &&
        prop10One(newMessages.getOrElse(x, Nil())) &&
        addWWProp10(messages, xs, c, m) &&
        prop10(newMessages, channels)
      case Cons(x,xs) => 
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop10One(newMessages.getOrElse(x, Nil())) &&
        addWWProp10(messages, xs, c, m) &&
        prop10(newMessages, channels)
    }
  
  }holds
  
  def addWWProp10One(
    list: List[Message],
    m: Message
  ): Boolean = {
    require(
      prop10One(list) && 
      {
        m match {
          case WriteWaiting(s,i,_,_) => 
            !collectWWs(list).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    
    list match {
      case Nil() => prop10One(list :+ m)
      case Cons(x@WriteWaiting(a,b,id,h), xs) => 
        !collectWWs(xs).contains(WriteUser(a,b)) &&
        addEndWW(xs, m, x) &&
        !collectWWs(xs :+ m).contains(WriteUser(a,b)) &&
        addWWProp10One(xs, m) &&
        prop10One(xs :+ m) &&
        prop10One(list :+ m) &&
        true
      case Cons(x,xs) => 
        addWWProp10One(xs, m) &&
        prop10One(xs :+ m) &&
        prop10One(list :+ m)
    }
  
  }holds
  
  def addEndWW(
    list: List[Message],
    mAdded: Message, 
    mHead: Message
    ): Boolean = {
    require(
      {
        mHead match {
          case WriteWaiting(a,b,id,h) => 
            mAdded match {
              case WriteWaiting(s,i,id,h) => 
                !collectWWs(list).contains(WriteUser(a,b)) &&
                !collectWWs(list).contains(WriteUser(s,i)) &&
                (a,b) != (s,i)
              case _ => false
            }
          case _ => false
        } 
      }      
    )
    val WriteWaiting(a,b,id,h) = mHead
    
    list match {
      case Nil() => 
        !collectWWs(list :+ mAdded).contains(WriteUser(a,b))
      case Cons(x,xs) => 
        (x != mHead) &&
        addEndWW(xs, mAdded, mHead) &&
        !collectWWs(list :+ mAdded).contains(WriteUser(a,b))        
    }
    
  } holds
  
  def addOtherProp10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      {
        m match {
          case WriteWaiting(s,i,_,_) => 
            false
          case _ => true
        }
      } &&
      prop10(messages, channels)
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c) => 
        addOtherProp10One(messages.getOrElse(x, Nil()), m) &&
        prop10One(newMessages.getOrElse(x, Nil())) &&
        addOtherProp10(messages, xs, c, m) &&
        prop10(newMessages, channels)
      case Cons(x,xs) => 
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop10One(newMessages.getOrElse(x, Nil())) &&
        addOtherProp10(messages, xs, c, m) &&
        prop10(newMessages, channels)
    }
  }holds
  
  def addOtherProp10One(
    list: List[Message],
    m: Message
  ): Boolean = {
    require(
      prop10One(list) && 
      {
        m match {
          case WriteWaiting(s,i,_,_) => 
            false
          case _ => true
        }
      }
    )
    
    list match {
      case Nil() => prop10One(list :+ m)
      case Cons(x@WriteWaiting(s,i,_,_), xs) =>
        addCollect3One(xs, m) &&
        !collectWWs(xs :+ m).contains(WriteUser(s,i)) &&
        addOtherProp10One(xs, m) &&
        prop10One(list :+ m)
      case Cons(x, xs) =>
        addOtherProp10One(xs, m) &&
        prop10One(list :+ m)
    }
    
  }holds
  
  def addProp10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      {
        m match {
          case WriteWaiting(s,i,_,_) => 
            !collectWWs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i))
          case _ => true
        }
      } &&
      prop10(messages, channels)
    )
    val newMessages = add(messages, c, m)
    
    m match {
      case WriteWaiting(s,i,_,_) => 
        addWWProp10(messages, channels, c, m) &&
        prop10(newMessages, channels)
      case _ => 
        addOtherProp10(messages, channels, c, m) &&
        prop10(newMessages, channels)
    }
  
  }holds
  
  def theoremProp10(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    s: Variable,
    i: BigInt
  ): Boolean = {
    require(
      !collectWWsList(messages, channels).contains(WriteUser(s,i)) &&
      channels.contains(c)
    )
    
    channels match {
      case Cons(x,xs) if (x == c) =>
        !collectWWs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i))
      case Cons(x,xs) =>
        theoremProp10(messages, xs, c, s, i) &&
        !collectWWs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i))
    }
  
  }holds

  def initProp10(
    messages: MMap[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(collectWWsList(messages, channels).isEmpty)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWWs(messages.getOrElse(x, Nil())).isEmpty &&
        initProp10One(messages.getOrElse(x, Nil())) &&
        prop10One(messages.getOrElse(x, Nil())) &&
        initProp10(messages, xs) &&
        prop10(messages, channels)
    }
  }holds
  
  def initProp10One(
    list: List[Message]
  ): Boolean = {
    require(
      collectWWs(list).isEmpty
    )
    
    list match {
      case Nil() => true
      case Cons(x@WriteWaiting(_,_,_,_), xs) => false
      case Cons(x,xs) =>
        initProp10One(xs) &&
        prop10One(list)
    }
  }holds
 
}
