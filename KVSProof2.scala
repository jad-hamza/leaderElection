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

object ProtocolProof2 {
  import Protocol._
  import PrettyPrinting._
  import ProtocolProof._
  
  
  // property 6
// WU(id) in C(i,j) => not WW(id) in C(k,l)

  def prop6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    (collectWUsList(messages, channels) & collectWWsList(messages,channels)).isEmpty
  }
  
  def collectWWs(l: List[Message]): Set[Message] = {
    l match {
      case Nil() => Set()
      case Cons(x@WriteWaiting(s,i,id,h), xs) => collectWWs(xs) ++ Set(WriteUser(s,i))
      case Cons(_,xs) => collectWWs(xs)
    }
  }
  
  def collectWWsList(
    messages: MMap[(ActorId,ActorId),List[Message]], 
    channels: List[(ActorId,ActorId)]
  ): Set[Message] = {
    channels match {
      case Nil() => Set()
      case Cons(c,cs) => 
        collectWWs(messages.getOrElse(c,Nil())) ++ collectWWsList(messages,cs)
    }
  }
  
//   def removeWUprop6(
//     messages: MMap[(ActorId,ActorId),List[Message]],
//     c: (ActorId, ActorId),
//     channels: List[(ActorId, ActorId)]
//   ): Boolean = {
//     require(
//       distinctElements[(ActorId, ActorId)](channels) &&
//       channels.contains(c) &&
//       {
//         messages.getOrElse(c, Nil()) match {
//           case Nil() => false
//           case Cons(WriteUser(s,i), xs) => true
//           case _ => false
//         }
//       } &&
//       uniqueWriteUser(messages, channels) &&
//       not2WriteUser(channels, messages) &&
//       prop6(messages, channels)
//     )
//     
//     val Cons(WriteUser(s,i),newChannel) = messages.getOrElse(c, Nil())
//     val newMessages = messages.updated(c, newChannel)
//     
//     channels match {
//       case Nil() => true
//       case Cons(x,xs) if(x==c) => 
//         theorem(messages.getOrElse(c,Nil()),WriteUser(s,i)) &&
//         // messages(c).contains(WU(s,i))
//         !collectWUsList(messages, xs).contains(WriteUser(s,i)) &&
//         // WU(s,i) is not in another channels than c
//         removeNot2WriteUserBis(messages, c._1, c._2, channels) &&
//         // !newMessages(c) contains(WU(s,i)) && not2WriteUser(channels, newMessages)
//         !newMessages.getOrElse(c,Nil()).contains(WriteUser(s,i)) &&
//         equivTheorem(newMessages.getOrElse(c,Nil()), WriteUser(s,i)) &&
//         // !collectWUs(c).contains(WU(s,i))
//         lemma(messages, c, xs) &&
//         // if !channels.contains(c) then collectWUs(messages) == collectWUs(newMessages)
//         !collectWUsList(newMessages, channels).contains(WriteUser(s,i)) &&
//         removeCollectWW(messages, channels, c) &&
//         // collectWSsList(newMessages) subset of collectWSsList(messages)
//         removeCollectWU(messages, channels, c) &&
//         // collectWUsList(newMessages) subset of collectWUsList(messages)
//         prop6(newMessages, channels) &&
//         true
//         
//       case Cons(x,xs) => 
//         removeWUprop6(messages, c, xs) &&
//         theorem2(c, xs, WriteUser(s,i), messages) &&
//         !collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && {
//         if (messages.getOrElse(x,Nil()).contains(WriteUser(s,i))){
//           theorem(messages.getOrElse(x,Nil()), WriteUser(s,i))
//           !collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && false
//         }
//         else {
//           !messages.getOrElse(x,Nil()).contains(WriteUser(s,i))
//         }
//         } &&
//         equivTheorem(newMessages.getOrElse(x, Nil()), WriteUser(s,i))&&
//         !collectWUsList(newMessages, channels).contains(WriteUser(s,i)) &&
//         removeCollectWW(messages, channels, c) &&
//         removeCollectWU(messages, channels, c) &&
//         prop6(newMessages, channels)
//     }    
//   } holds
  
  def removeCollectWW(
    messages: MMap[(ActorId,ActorId),List[Message]], 
    channels: List[(ActorId,ActorId)],
    c: (ActorId,ActorId)
  ): Boolean = {
    require(!messages.getOrElse(c, Nil()).isEmpty)
    val Cons(x,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c,chan)
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        removeCollectWW(messages, xs, c) &&
        (collectWWsList(newMessages, channels) subsetOf collectWWsList(messages, channels))
    }
  }holds

  def theoremWS(l: List[Message], m: Message): Boolean = {
    if (
      m match {
        case WriteSystem(s,i,idM,h) => l.contains(m)
        case _ => false
      }
    ){
      val WriteSystem(d,v,idM,h) = m
      l match {
        case Nil() => false
        case Cons(x@WriteSystem(s,i,_,_), xs) if(x ==   m) =>
          collectWSs(l).contains(WriteUser(d,v))
        case Cons(_,xs) => 
          theoremWS(xs,m) &&
          collectWSs(l).contains(WriteUser(d,v))
      }
    }
    else true
  }holds
  
  def theorem3WS(
    messages: MMap[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    m: Message
  ): Boolean = {
    require(
      channels.contains(c) &&
      collectWSs(messages.getOrElse(c, Nil())).contains(m)
    )
    channels match {
      case Cons(x,xs) if (x ==c) => 
        collectWSsList(messages, channels).contains(m)
      case Cons(x,xs) => 
        theorem3WS(messages, c, channels, m) &&
        collectWSsList(messages, channels).contains(m)
    }
  } holds
  
  def removeWSprop6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      prop6(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteSystem(s,i,idM,h), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val WriteSystem(s,i,idM,h) = m
    val newMessages = messages.updated(c, newChan)
    
    theoremWS(messages.getOrElse(c, Nil()), m) &&
    collectWSs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i)) &&
    theorem3WS(messages, c, channels, WriteUser(s,i)) &&
    collectWSsList(messages, channels).contains(WriteUser(s,i)) &&
    !collectWUsList(messages, channels).contains(WriteUser(s,i)) &&
    removeCollectWU(messages, channels, c) &&
    !collectWUsList(newMessages, channels).contains(WriteUser(s,i)) &&
    true
  }holds
  
  def theoremWW(l: List[Message], m: Message): Boolean = {
    if (
      m match {
        case WriteWaiting(s,i,idM,h) => l.contains(m)
        case _ => false
      }
    ){
      val WriteWaiting(d,v,idM,h) = m
      l match {
        case Nil() => false
        case Cons(x@WriteWaiting(s,i,_,_), xs) if(x ==  m) =>
          collectWWs(l).contains(WriteUser(d,v))
        case Cons(_,xs) => 
          theoremWW(xs,m) &&
          collectWWs(l).contains(WriteUser(d,v))
      }
    }
    else true
  }holds
  
  def theorem3WW(
    messages: MMap[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    m: Message
  ): Boolean = {
    require(
      channels.contains(c) &&
      collectWWs(messages.getOrElse(c, Nil())).contains(m)
    )
    channels match {
      case Cons(x,xs) if (x ==c) => 
        collectWWsList(messages, channels).contains(m)
      case Cons(x,xs) => 
        theorem3WW(messages, c, channels, m) &&
        collectWWsList(messages, channels).contains(m)
    }
  } holds
  
  def removeWWprop6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      prop6(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteWaiting(s,i,idM,h), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val WriteWaiting(s,i,idM,h) = m
    val newMessages = messages.updated(c, newChan)
    
    theoremWW(messages.getOrElse(c, Nil()), m) &&
    collectWWs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i)) &&
    theorem3WW(messages, c, channels, WriteUser(s,i)) &&
    collectWWsList(messages, channels).contains(WriteUser(s,i)) &&
    !collectWUsList(messages, channels).contains(WriteUser(s,i)) &&
    true
    
  }holds
  
  
  def removeAllProp6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop6(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )
    
    val Cons(m,newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        removeCollectWU(messages, channels, c) && 
        removeCollectWW(messages, channels, c) &&
        prop6(newMessages, xs)
    }
  }holds
  
  def removeProp6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      prop6(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty &&
      channels.contains(c)
    )
    val Cons(m,xs) = messages.getOrElse(c, Nil())
    
    m match {
      case WriteSystem(s,i,idM,h) => 
        removeAllProp6(messages, channels, c) //&&
        // prop6 is maintained
        removeWSprop6(messages, channels, c)
        // no WU(id) in channels
      case WriteWaiting(s,i,idM,h) =>
        removeAllProp6(messages, channels, c) //&&
        // prop6 is maintained
        removeWWprop6(messages, channels, c)
        // no WU(id) in channels
      case _ => 
        removeAllProp6(messages, channels, c)
    }
  } holds
  
  @induct
  def addCollect3One(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteWaiting(s,i,id,h) => false 
        case _ => true
      }
    })
    collectWWs(l) == collectWWs(l :+ m)       
  } holds
  
  def addCollect3(messages: MMap[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteWaiting(s,i,id,h) => false 
        case _ => true
      }
    })

    channels match {
      case Nil() => 
        collectWWsList(messages,channels) == collectWWsList(add(messages, c, m), channels)
      case Cons(d,ds) =>
      	addCollect3(messages, c, m, ds) &&
        addCollect3One(messages.getOrElse(d,Nil()), m) &&
        collectWWsList(messages,channels) == collectWWsList(add(messages, c, m), channels)        
    }
    
  } holds
  
  def addOtherProp6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop6(messages, channels) &&
      {
        m match {
          case WriteUser(s,i) => false
          case WriteWaiting(s,i,id,h) => false
          case _ => true
        }
      }
    )
    val newMessages = add(messages, c, m)
    addCollect(messages, c, m, channels) &&
    collectWUsList(newMessages, channels) == collectWUsList(messages, channels) &&
    addCollect3(messages, c, m, channels) &&
    collectWWsList(newMessages, channels) == collectWWsList(messages, channels) &&
    prop6(newMessages, channels)    
  
  } holds

    @induct
  def addCollectOneWW(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteWaiting(s,i, id, h) => true 
        case _ => false
      }
    })
    val WriteWaiting(s,i,id,h) = m
    collectWWs(l) ++Set(WriteUser(s,i)) == collectWWs(l :+ m)       
  } holds
  
  def addCollectWW(messages: MMap[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteWaiting(s,i,id,h) => true 
        case _ => false
      }
    })

    val WriteWaiting(s,i,id,h) = m
    
    channels match {
      case Nil() => 
        true
      case Cons(d,ds) =>
        addCollectWW(messages, c, m, ds) &&
        addCollectOneWW(messages.getOrElse(d,Nil()), m) &&
        {
          if (channels.contains(c)) {
            collectWWsList(messages,channels) ++Set(WriteUser(s,i)) == collectWWsList(add(messages, c, m), channels)
          }
          else {
            collectWWsList(messages,channels) == collectWWsList(add(messages, c, m), channels)
          }
        }
    }
  } holds  
  
  def addWWProp6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop6(messages, channels) &&
      {
        m match {
          case WriteWaiting(s,i, idM, h) => 
            !collectWUsList(messages, channels).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    
    val newMessages = add(messages, c, m)
    
    addCollect(messages, c, m, channels) &&
    addCollectWW(messages, c, m, channels) &&
    prop6(newMessages, channels)
  } holds
  
  def addWUprop6(
    messages: MMap[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop6(messages, channels) &&
      !collectWWsList(messages, channels).contains(m) &&
      {
        m match {
          case WriteUser(s,i) => true
          case _ => false
        }
      }
    )
    
    val newMessages = add(messages, c, m)
    
    addCollect3(messages, c, m, channels) &&
    addCollectWU(messages, c, m, channels) &&
    prop6(newMessages, channels)
    
  } holds
  
  
}
