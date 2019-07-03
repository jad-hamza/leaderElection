package distribution


import FifoNetwork._
import Networking._
import Protocol._

import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._
import stainless.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof2 {
  import Protocol._
  import PrettyPrinting._
  import ProtocolProof._
  
  
  // property 6
// WU(id) in C(i,j) => not WW(id) in C(k,l)

  def prop6(
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]], 
    channels: List[(ActorId,ActorId)]
  ): Set[Message] = {
    channels match {
      case Nil() => Set()
      case Cons(c,cs) => 
        collectWWs(messages.getOrElse(c,Nil())) ++ collectWWsList(messages,cs)
    }
  }
  
  def removeCollectWW(
    messages: Map[(ActorId,ActorId),List[Message]], 
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
  
  def addCollect3(
    messages: Map[(ActorId,ActorId),List[Message]], 
    c: (ActorId,ActorId),
    m: Message, 
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
  
  def addCollectWW(messages: Map[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
  
  
// property 7
// WS in C(i,j) => not WS in C(i',j)
  def prop7(
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        (collectWSs(messages.getOrElse(x, Nil())) & collectNeighbour(x._2,xs, messages)).isEmpty &&
        prop7(xs, messages)
    }
  }

  def collectNeighbour(
    id: ActorId,
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]]
  ): Set[Message] = {
    channels match {
      case Nil() => Set()
      case Cons(x,xs) if (x._2 == id) =>
        collectWSs(messages.getOrElse(x, Nil())) ++ collectNeighbour(id, xs, messages)
      case Cons(x,xs) =>  
        collectNeighbour(id,xs,messages)
    }
  }
  
  def addWSprop7(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop7(channels, messages) &&
      {
        m match {
          case WriteSystem(s,i,idM,h) => 
            !collectNeighbour(c._2, channels, messages).contains(WriteUser(s,i))
          case _ => false
        }
      } &&
      distinctElements[(ActorId, ActorId)](channels)
    )
    val newMessages = add(messages, c, m)
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c)  =>
        addCollectOneWS(messages.getOrElse(c, Nil()),m) &&
        addCollectNeighbourWS(messages, c._2, c, m, channels) &&
        (collectWSs(newMessages.getOrElse(c, Nil())) & collectNeighbour(c._2,xs, newMessages)).isEmpty &&
        addWSprop7(messages, channels, c, m) &&
        prop7(channels, newMessages) &&
        true
      case Cons(x,xs) => 
        addCollectNeighbourWS(messages, x._2, c, m, channels) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectNeighbour(x._2,xs, newMessages)).isEmpty &&
        addWSprop7(messages, channels, c, m) &&
        prop7(channels, newMessages) &&
        true
    }
    
  }holds
  
  
  def addCollectNeighbourWS(
    messages: Map[(ActorId,ActorId),List[Message]],
    id: ActorId,
    c: (ActorId,ActorId), 
    m: Message, 
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    require({
      m match {
        case WriteSystem(s,i,id,h) => true 
        case _ => false
      }
    })

    val WriteSystem(s,i,_,_) = m
    
    channels match {
      case Nil() => 
        true
      case Cons(d,ds) =>
        addCollectNeighbourWS(messages, id,  c, m, ds) &&
        addCollectOneWS(messages.getOrElse(d,Nil()), m) &&
        {
          if (c._2 == id && channels.contains(c)) {
            collectNeighbour(id, channels, messages) ++Set(WriteUser(s,i)) == collectNeighbour(id, channels, add(messages, c, m))
          }
          else {
            collectNeighbour(id, channels, messages) == collectNeighbour(id, channels, add(messages, c, m))
          }
        }
    }
  } holds
  
  def addCollectNeighbour(
    messages: Map[(ActorId,ActorId),List[Message]],
    id: ActorId,
    c: (ActorId,ActorId), 
    m: Message, 
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    require(
      m match {
        case WriteSystem(s,i,id,h) => false 
        case _ => true
      }
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(d,ds) => 
        addCollectNeighbour(messages, id, c, m, ds) &&
        addCollect2One(messages.getOrElse(d, Nil()), m) &&
        collectNeighbour(id, channels, messages) == collectNeighbour(id, channels, add(messages, c, m))
    }
    
  }holds
  
  def addOtherprop7(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop7(channels, messages) &&
      {
        m match {
          case WriteSystem(s,i,idM,h) => false
          case _ => true
        }
      } &&
      distinctElements[(ActorId, ActorId)](channels)
    )
    val newMessages = add(messages, c, m)
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c)  =>
        addCollect2One(messages.getOrElse(c, Nil()),m) &&
        addCollectNeighbour(messages, c._2, c, m, channels) &&
        (collectWSs(newMessages.getOrElse(c, Nil())) & collectNeighbour(c._2,xs, newMessages)).isEmpty &&
        addOtherprop7(messages, channels, c, m) &&
        prop7(channels, newMessages) &&
        true
      case Cons(x,xs) => 
        addCollectNeighbour(messages, x._2, c, m, channels) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectNeighbour(x._2,xs, newMessages)).isEmpty &&
        addOtherprop7(messages, channels, c, m) &&
        prop7(channels, newMessages) &&
        true
    }
    
  }holds
  
  def addProp7(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop7(channels, messages) &&
      {
        m match {
          case WriteSystem(s,i,idM,h) => 
            !collectNeighbour(c._2, channels, messages).contains(WriteUser(s,i))
          case _ => true
        }
      } &&
      distinctElements[(ActorId, ActorId)](channels)
    )
    
    m match {
      case WriteSystem(s,i,idM,h) => 
        addWSprop7(messages, channels, c, m) &&
        prop7(channels, add(messages, c, m))
      case _ => 
        addOtherprop7(messages, channels, c, m) &&
        prop7(channels, add(messages, c, m))
    }
  } holds
  
  def removeCollectNeighbour(
    id: ActorId,
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(!messages.getOrElse(c, Nil()).isEmpty)
    
    val Cons(x,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c,chan)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        removeCollectNeighbour(id, messages, xs, c) &&
        (collectNeighbour(id, channels, newMessages) subsetOf collectNeighbour(id, channels, messages))
    }
  }holds
  
  def removeProp7(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop7(channels, messages) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )
    
    val Cons(m,newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWSs(newMessages.getOrElse(x, Nil())).subsetOf(collectWSs(messages.getOrElse(x, Nil()))) &&
        removeCollectNeighbour(x._2, messages, channels, c) &&
        collectNeighbour(x._2,xs, newMessages).subsetOf(collectNeighbour(x._2,xs, messages)) &&
        removeProp7(messages, xs, c) &&
        prop7(channels, newMessages) &&
        true
    }
  } holds
  
  def collectOtherActorProp7(
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message
  ): Boolean = {
    otherActor match {
      case Nil() => true
      case Cons(x,xs) => 
        !collectNeighbour(x, channels, messages).contains(m) &&
        collectOtherActorProp7(xs, messages, m)
    }
  }
  
  def leMaprop7(
    id: ActorId,
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    s: Variable, i: BigInt
  ): Boolean = {
    require (
      areInChannels(id, otherActor) &&
      !collectWSsList(messages, channels).contains(WriteUser(s,i))
    )
    
    otherActor match {
      case Nil() => true
      case Cons(x,xs) => 
        collectOtherActorOneProp7(x,messages,WriteUser(s,i),channels) &&
        !collectNeighbour(x, channels, messages).contains(WriteUser(s,i)) &&
        leMaprop7(id, xs, messages, s, i) &&
        collectOtherActorProp7(otherActor, messages, WriteUser(s,i)) &&
        true
    }
   }holds
   
  def collectOtherActorOneProp7(
    id: ActorId, 
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message, 
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(
      //channels.contains((id1,id2)) &&
      !collectWSsList(messages, channels).contains(m)
    )
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) =>
        !collectWSs(messages.getOrElse(x, Nil())).contains(m) &&
        collectOtherActorOneProp7(id, messages, m, xs) &&
        !collectNeighbour(id, channels, messages).contains(m)
      case Cons(x,xs) => 
        collectOtherActorOneProp7(id, messages, m, xs) && 
        !collectNeighbour(id, channels, messages).contains(m)
    }
  }holds
  
  def initProp7(
    messages: Map[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(collectWSsList(messages, channels).isEmpty)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWSs(messages.getOrElse(x, Nil())).isEmpty &&
        initProp7(messages, xs) &&
        prop7(channels, messages)
    }
  }holds
  
  def broadcastAckPreInductProp7(
    id: ActorId, 
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message
  ): Boolean = {
    require(
      distinctElements[ActorId](otherActor) &&
      {
        m match {
          case WriteSystem(s,i,_idM,h) => 
            collectOtherActorProp7(otherActor, messages, WriteUser(s,i))
          case _ => false
        }
      }
    )
    val WriteSystem(s,i,idM,h) = m
  
    otherActor match {
      case Nil() => true
      case Cons(x, Nil()) => 
        collectOtherActorProp7(Nil() , add(messages, (id,x), m), WriteUser(s,i))
      case Cons(x,Cons(y,ys)) => 
        addInduct(messages, (id,x), y, m, channels) &&
        collectNeighbour(y, channels, messages) == collectNeighbour(y, channels, add(messages, (id,x), m)) &&
        broadcastAckPreInductProp7(id, Cons(x,ys), messages, m) &&
        collectOtherActorProp7(Cons(y,ys), add(messages, (id,x),m), WriteUser(s,i)) &&
        true
    }
  
  }holds
  
  def addInduct(
    messages: Map[(ActorId, ActorId), List[Message]],
    c: (ActorId, ActorId),
    id: ActorId,
    m: Message, 
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(
      c._2 != id
    )
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) =>
        messages.getOrElse(x, Nil()) == add(messages, c, m).getOrElse(x, Nil()) &&
        addInduct(messages, c, id, m, xs) &&
        collectNeighbour(id, channels, messages) == collectNeighbour(id, channels, add(messages, c, m))
      case Cons(x,xs) =>
        addInduct(messages, c, id, m, xs) &&
        collectNeighbour(id, channels, messages) == collectNeighbour(id, channels, add(messages, c, m))
    }
  
  }holds
  
  
  
// property 4
// WU(id) in C(i,j) => not id in h_j

// sketch proof:
// - receiving a WU(id) there are no WS, WW, other WU in channels
// - receiving a WS(id) or a WW(id) there is no WU(id) in channels
// ==> remove WU -> no WU (already proved in property 1
// ==> remove (WS or WW) -> no WU

// adding a WU(id) in C(i,j) there is not id in h_k (for all k)


  def allHistoriesContainsAux(
    s: Variable,
    i: BigInt, 
    actors: List[ActorId],
    states: Map[ActorId, State]
  ): Boolean = {
    actors match {
      case Nil() => false
      case Cons(x, xs) => 
        states.getOrElse(x, BadState()) match {
          case CommonState(mem,h) => 
            h.contains((true, s, i)) ||
            allHistoriesContainsAux(s, i, xs, states)
          case _ =>   
            allHistoriesContainsAux(s,i,xs, states)
        }
    }
  }
  
  def notAllHistoriesContainsEmptyAux(
    s: Variable,
    i: BigInt, 
    actors: List[ActorId]
  ): Boolean = {
    actors match {
      case Nil() => true
      case Cons(x, xs) => 
        initStates.getOrElse(x, BadState()) match {
          case CommonState(mem,h) => 
            h.isEmpty &&
            !h.contains((true, s, i)) &&
            notAllHistoriesContainsEmptyAux(s, i, xs) &&
            !allHistoriesContainsAux(s,i,actors, initStates) &&
            true
          case _ => 
            notAllHistoriesContainsEmptyAux(s,i,xs) && 
            !allHistoriesContainsAux(s,i,actors, initStates) &&
            true
        }
    }
  }holds
  
  def updateSystemAllHistoriesContainsAux(
    s: Variable,
    i: BigInt, 
    actors: List[ActorId],
    states: Map[ActorId, State], 
    id: ActorId, 
    x: Variable, v: BigInt
  ): Boolean = {
    require(
      !allHistoriesContainsAux(s, i, actors, states) &&
      {
        states.getOrElse(id, BadState()) match {
          case CommonState(mem, h) => true
          case _ => false
        }
      } &&
      (s,i) != (x,v)
    )
    val CommonState(mem, h) = states.getOrElse(id, BadState())
    val newStates = states.updated(id, CommonState(mem.updated(x,v),h++Set((true,x,v))))
    
    actors match {
      case Nil() => true
      case Cons(d,ds) if (d == id) => 
        !h.contains((true, s, i)) &&
        (s,i) != (x,v) &&
        !(h ++ Set((true,x,v))).contains((true,s,i)) &&
        updateSystemAllHistoriesContainsAux(s,i,ds, states,  id, x, v) &&
        !allHistoriesContainsAux(s,i,actors, newStates)
      case Cons(d,ds) => 
        states.getOrElse(d, BadState()) == newStates.getOrElse(d, BadState()) &&
        updateSystemAllHistoriesContainsAux(s,i,ds, states,  id, x, v) &&
        !allHistoriesContainsAux(s,i,actors, newStates)
    }
  
  }holds
  
  def updateUserAllHistoriesContainsAux(
    s: Variable,
    i: BigInt, 
    actors: List[ActorId],
    states: Map[ActorId, State], 
    id: ActorId, 
    state: State
  ): Boolean = {
    require(
      !allHistoriesContainsAux(s,i,actors, states) &&
      {
        state match {
        case UserState(h,c) => true
        case _ => false
        }
      }
    )
    val newStates = states.updated(id, state)
    
    actors match {
      case Nil() => true
      case Cons(x,xs) if (x == id) => 
        newStates.getOrElse(id, BadState()) match {
          case UserState(h,c) => 
            updateUserAllHistoriesContainsAux(s,i,xs, states, id, state) &&
            !allHistoriesContainsAux(s,i,actors, newStates)
          case _ => false
        }
      case Cons(x,xs) =>  
        states.getOrElse(x, BadState()) == newStates.getOrElse(x, BadState()) &&
        updateUserAllHistoriesContainsAux(s,i,xs, states,  id, state) &&
        !allHistoriesContainsAux(s,i,actors, newStates)
    }
  
  }holds
  
  def prop4(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)], 
    actors: List[ActorId]
  ): Boolean = {
  
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        prop4One(messages.getOrElse(x, Nil()), states, actors) &&
        prop4(messages, states, xs, actors)
    }
    
  }
  
  def prop4One(
    list: List[Message], 
    states: Map[ActorId, State],
    actors: List[ActorId]
  ): Boolean = {
    
    list match {
      case Nil() => true
      case Cons(m,xs) => 
        m match {
          case WriteUser(s,i) => 
            !allHistoriesContainsAux(s, i, actors, states) &&
            prop4One(xs, states, actors)
          case _ => 
            prop4One(xs, states, actors)
        }
    }
  }
  
  def initProp4(
   messages: Map[(ActorId, ActorId), List[Message]],
   channels: List[(ActorId, ActorId)], 
   states: Map[ActorId, State], 
   actors: List[ActorId]
  ): Boolean = {
    require(
      collectWUsList(messages, channels).isEmpty
    )
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWUs(messages.getOrElse(x, Nil())).isEmpty &&
        initProp4One(messages.getOrElse(x, Nil()), actors, states) &&
        initProp4(messages, xs, states, actors) &&
        prop4(messages, states, channels, actors)
    }
  }holds
  
  def initProp4One(
    list: List[Message],
    actors: List[ActorId], 
    states: Map[ActorId, State]
  ): Boolean = {
    require(
      collectWUs(list).isEmpty
    )
  
    list match {
      case Nil() => true
      case Cons(m,xs) => 
        m match {
          case WriteUser(s,i) => false
          case _ => 
            initProp4One(xs, actors, states) &&
            prop4One(list, states, actors)
        }
    }
  
  }holds
  
  def addWUprop4One(
    list: List[Message],
    m: Message,
    actors: List[ActorId], 
    states: Map[ActorId, State]
  ): Boolean = {
    require(
      prop4One(list, states, actors) &&
      isWU(m) && 
      {
        val WriteUser(s,i) = m
        !allHistoriesContainsAux(s,i,actors, states)
      }
    )
    
    list match {
      case Nil() => 
        prop4One(list :+ m, states, actors)
      case Cons(x,xs) => 
        x match {
          case WriteUser(s,i) => 
            !allHistoriesContainsAux(s,i,actors, states) &&
            addWUprop4One(xs, m, actors, states) &&
            prop4One(list :+ m, states, actors)
          case _ => 
            addWUprop4One(xs, m, actors, states) &&
            prop4One(list :+ m, states, actors)
        }
    }
    
  }holds
  
  def addWUprop4(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    states: Map[ActorId, State],
    c: (ActorId, ActorId),
    m: Message, 
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
      isWU(m) && 
      {
        val WriteUser(s,i) = m
        !allHistoriesContainsAux(s,i,actors, states)
      }
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        addWUprop4One(messages.getOrElse(x, Nil()), m, actors, states) &&
        prop4One(messages.getOrElse(x, Nil()), states, actors) &&
        addWUprop4(messages, xs, states, c, m, actors) &&
        prop4(newMessages, states, channels, actors) &&
        true
      case Cons(x,xs) =>
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        prop4One(newMessages.getOrElse(x, Nil()), states, actors) &&
        addWUprop4(messages, xs, states, c, m, actors) &&
        prop4(newMessages, states, channels, actors) &&
        true
    }
  
  }holds
  
  def addOtherProp4One(
    list: List[Message], 
    m: Message, 
    actors: List[ActorId],
    states: Map[ActorId, State]
  ): Boolean = {
    require(
      !isWU(m) &&
      prop4One(list, states, actors)
    )
    
    list match {
      case Nil() => prop4One(list :+ m, states, actors)
      case Cons(x,xs) => 
        x match {
          case WriteUser(s,i) => 
            !allHistoriesContainsAux(s,i,actors, states) &&
            addOtherProp4One(xs, m, actors, states) &&
            prop4One(list :+ m, states, actors)
          case _ => 
            addOtherProp4One(xs, m, actors, states)
            prop4One(list :+ m, states, actors)
        }
    }
  }holds
  
  def addOtherProp4(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    states: Map[ActorId, State],
    c: (ActorId, ActorId),
    m: Message,
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
      !isWU(m)
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (c == x) => 
        addOtherProp4One(messages.getOrElse(x, Nil()), m, actors, states) &&
        prop4One(newMessages.getOrElse(x, Nil()), states, actors) &&
        addOtherProp4(messages, xs, states, c, m, actors) &&
        prop4(newMessages, states, channels, actors)
      case Cons(x,xs) => 
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop4One(newMessages.getOrElse(x, Nil()), states, actors) &&
        addOtherProp4(messages, xs, states, c, m, actors) &&
        prop4(newMessages, states, channels, actors)
    }
  
  }holds
  
  def updateStateUserProp4One(
    list: List[Message], 
    actors: List[ActorId],
    id: ActorId,
    states: Map[ActorId, State],
    newState: State
  ): Boolean = {
    require(
      prop4One(list, states, actors) &&
      {
        newState match {
        case UserState(h,c) => true
        case _ => false
        }
      }
    )
    val newStates = states.updated(id, newState)
    
    list match {
      case Nil() => true
      case Cons(m,xs) => 
        m match {
          case WriteUser(s,i) => 
            updateUserAllHistoriesContainsAux(s,i,actors, states, id, newState) &&
            updateStateUserProp4One(xs, actors, id, states, newState) &&
            prop4One(list, newStates, actors)
          case _ => 
            updateStateUserProp4One(xs, actors, id, states, newState) &&
            prop4One(list, newStates, actors)
        }
    }
  
  }holds
  
  def updateStateUserProp4(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    states: Map[ActorId, State],
    id: ActorId,
    m: State, 
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
      {
        m match {
          case UserState(h,c) => true
          case _ => false
        }
      }
    )
    val newStates = states.updated(id, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        updateStateUserProp4One(messages.getOrElse(x, Nil()), actors, id, states, m) &&
        prop4One(messages.getOrElse(x, Nil()), states, actors) &&
        updateStateUserProp4(messages, xs, states, id, m, actors) &&
        prop4(messages, newStates, channels, actors)
    }
    
  }holds
  
  def updateStateSystemProp4One(
    list: List[Message], 
    actors: List[ActorId],
    states: Map[ActorId, State],
    id: ActorId,
    s: Variable, 
    i: BigInt
  ): Boolean = {
    require(
      !list.contains(WriteUser(s,i)) &&
      prop4One(list, states, actors) &&
      {
        states.getOrElse(id, BadState()) match {
          case CommonState(mem, h) => true
          case _ => false
        }
      }
    )
    val CommonState(mem, h) = states.getOrElse(id, BadState())
    val newStates = states.updated(id, CommonState(mem.updated(s,i),h++Set((true,s,i))))
    
    list match {
      case Nil() => true
      case Cons(m,xs) => 
        m match {
          case WriteUser(x,v) if ((x,v) != (s,i))=> 
            updateSystemAllHistoriesContainsAux(x,v,actors,states,id,s,i) &&
            updateStateSystemProp4One(xs,actors,states, id,s,i) &&
            prop4One(list, newStates, actors)
          case WriteUser(x,v) => false 
          case _ => 
            updateStateSystemProp4One(xs,actors,states, id,s,i) &&
            prop4One(list, newStates, actors)
        }
    }
    
  }holds
  
  def updateStateSystemProp4(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    states: Map[ActorId, State],
    id: ActorId,
    s: Variable, 
    i: BigInt,
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
      !collectWUsList(messages, channels).contains(WriteUser(s,i)) &&
      {
        states.getOrElse(id, BadState()) match {
          case CommonState(mem, h) => true
          case _ => false
        }
      }
    )
    val CommonState(mem, h) = states.getOrElse(id, BadState())
    val newStates = states.updated(id, CommonState(mem.updated(s,i),h++Set((true,s,i))))
  
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        !collectWUs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        {
          if(messages.getOrElse(x,Nil()).contains(WriteUser(s,i))){
            theorem(messages.getOrElse(x, Nil()), WriteUser(s,i)) &&
            false
          }
          else {
            !messages.getOrElse(x,Nil()).contains(WriteUser(s,i)) &&
            updateStateSystemProp4One(messages.getOrElse(x, Nil()), actors, states, id, s, i) &&
            prop4One(messages.getOrElse(x, Nil()),states, actors) &&
            updateStateSystemProp4(messages, xs, states, id, s, i, actors) &&
            prop4(messages, newStates, channels, actors)
          }
        }
    }
  
  }holds
  
  def inductInitProp4(
    initList: List[(ActorId,Message)],
    states: Map[ActorId, State], 
    actors: List[ActorId]
  ): Boolean = {
    initList match {
      case Nil() => true
      case Cons((id,m),xs) => 
        m match {
          case WriteUser(s,i) => 
            !allHistoriesContainsAux(s,i,actors, states) &&
            inductInitProp4(xs, states, actors)
          case _ =>
            inductInitProp4(xs, states, actors) 
        }
    }
  }
  
  def updateInductInitProp4(
    initList: List[(ActorId,Message)],
    states: Map[ActorId, State], 
    messages: Map[(ActorId,ActorId),List[Message]], 
    actors: List[ActorId]
  ): Boolean = {
    require(
      areWU(initList) &&
      differentInitMessage(initList, messages) &&
      inductInitProp4(initList, states, actors) &&
      {
        initList match {
          case Cons((id,WriteUser(s,i)),xs) => true
          case _ => false
        }
      } &&
      {
        states.getOrElse(a4, BadState()) match {
          case UserState(h,c) => true
          case _ => false
        }
      }
    )
    val Cons((id,WriteUser(x,v)),ds) = initList
    val UserState(h,c) = states.getOrElse(a4, BadState())
    val newStates = states.updated(a4, UserState(Cons(((true, x,v),Set()), h), c))
    
    initList match {
      case Nil() => true
      case Cons((a,b), Nil()) => 
        b match {
          case WriteUser(s,i) => 
            inductInitProp4(Nil(), newStates, actors)
        }   
      case Cons((a,b),Cons((e,d), ys)) => 
        d match {
          case WriteUser(s,i) => 
            !allHistoriesContainsAux(s,i,actors, states) &&
            updateUserAllHistoriesContainsAux(s,i,actors, states, a4, UserState(Cons(((true, x,v),Set()), h), c)) &&
            !allHistoriesContainsAux(s,i,actors, newStates) &&
            updateInductInitProp4(Cons((a,b), ys), states, messages, actors) &&
            inductInitProp4(Cons((e,d), ys), newStates, actors)
        }   
    }
  
  }holds
  
  def inductInitProp4Empty(
    initList: List[(ActorId,Message)], 
    actors: List[ActorId]
  ): Boolean = {
    initList match {
      case Nil() => true
      case Cons((id,m),xs) =>
        m match {
          case WriteUser(s,i) => 
            notAllHistoriesContainsEmptyAux(s,i,actors) &&
            inductInitProp4Empty(xs, actors) &&
            inductInitProp4(xs, initStates,actors)
          case _ =>
            inductInitProp4Empty(xs, actors)
            inductInitProp4(xs, initStates, actors) 
        }
    }
  
  }holds
  
  def removeProp4(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    states: Map[ActorId, State],
    c: (ActorId, ActorId), 
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )
    val Cons(m,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, chan)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) =>
        prop4One(newMessages.getOrElse(x, Nil()), states, actors) &&
        removeProp4(messages, xs, states, c, actors) &&
        prop4(newMessages, states, channels, actors)
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop4One(newMessages.getOrElse(x, Nil()), states, actors) &&
        removeProp4(messages, xs, states, c, actors) &&
        prop4(newMessages, states, channels, actors)
    }
    
  }holds
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
// property 9
// WS(id) in C(i,j) => not(WW(id) in C(j,j))

// sketch of the proof:
// - (i)  remove WS => not(WS) in C(i,j) (prop5)
// - (ii) remove WS => not(WS in C(j,j) (prop7)
// ==> can add WW

// - (iii) remove WU => not(WW) (prop6)
// ==> can add WS

// -(iv) remove WW => not(WS)
// ==> can add WW

  def prop9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        (collectWSs(messages.getOrElse(x, Nil())) & collectWWs(messages.getOrElse((x._2, x._2), Nil()))).isEmpty &&
        prop9(messages, xs)
    }
  }

  // (i)
  def removeWSprop9_1(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop5(messages, channels) &&
      {
       messages.getOrElse(c, Nil()) match {
          case Cons(WriteSystem(s,i,_,_), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(WriteSystem(s,i,_,_),ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
  
    channels match {
      case Cons(x,xs) if (x==c) => 
        !collectWSs(newMessages.getOrElse(c, Nil())).contains(WriteUser(s,i))
      case Cons(x,xs) =>
        removeWSprop9_1(messages, xs, c) &&
        !collectWSs(newMessages.getOrElse(c, Nil())).contains(WriteUser(s,i))        
    }
  
  }holds
  
  def leMaprop9(
    c: (ActorId,ActorId), 
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    m: Message
  ): Boolean = {
    require(
      messages.getOrElse(c, Nil()).contains(m) &&
      channels.contains(c) &&
      {
        m match {
          case WriteSystem(s,i,_,_) => true
          case _ => false
        }
      }
      
    )
    val WriteSystem(s,i,_,_) = m
    
    channels match {
      case Cons(x,xs) if (x==c) => 
        theoremWS(messages.getOrElse(c, Nil()), m) &&
        collectWSs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i)) &&
        collectNeighbour(c._2, channels, messages).contains(WriteUser(s,i))
      case Cons(x,xs) =>
        leMaprop9(c, xs, messages, m) &&
        collectNeighbour(c._2, channels, messages).contains(WriteUser(s,i))
    }
    
  }holds
  
  // (i) and (ii)
  def removeWSprop9_2(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop5(messages, channels) &&
      prop7(channels, messages) &&
      {
       messages.getOrElse(c, Nil()) match {
          case Cons(WriteSystem(s,i,_,_), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(WriteSystem(s,i,idM,h),ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        removeWSprop9_1(messages, channels, c) &&
        !collectWSs(newMessages.getOrElse(c, Nil())).contains(WriteUser(s,i)) &&
        !collectNeighbour(c._2, xs, messages).contains(WriteUser(s,i)) &&
        removeCollectNeighbour(c._2, messages, channels, c) &&
        !collectNeighbour(c._2, xs, newMessages).contains(WriteUser(s,i)) &&
        !collectNeighbour(c._2, channels, newMessages).contains(WriteUser(s,i)) &&
        true
      case Cons(x,xs) if (x._2 == c._2) => 
        leMaprop9(c, channels, messages, WriteSystem(s,i,idM,h)) &&
        collectNeighbour(c._2, channels, messages).contains(WriteUser(s,i))&&
        !collectWSs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        !collectWSs(newMessages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        removeWSprop9_2(messages, xs, c) &&
        !collectNeighbour(c._2, channels, newMessages).contains(WriteUser(s,i)) &&
        true
      case Cons(x,xs) => 
        removeWSprop9_2(messages, xs, c) &&
        !collectNeighbour(c._2, channels, newMessages).contains(WriteUser(s,i)) &&
        true
    }
  
  }holds
  
  def addWWProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    id: ActorId,
    m: Message
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      {
        m match {
          case WriteWaiting(s,i,_,_) =>  
            !collectNeighbour(id, channels, messages).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    val newMessages = add(messages, (id,id), m)
    val WriteWaiting(s,i,_,_) = m
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) => 
        !collectWSs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        addCollect2One(messages.getOrElse(x, Nil()), m) &&
        !collectWSs(newMessages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        addCollectOneWW(messages.getOrElse((id,id), Nil()), m) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectWWs(newMessages.getOrElse((x._2, x._2), Nil()))).isEmpty &&
        addWWProp9(messages, channels, id, m) &&
        prop9(newMessages, channels) &&
        true
        
      case Cons(x,xs) => 
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        collectWSs(messages.getOrElse(x, Nil())) == collectWSs(newMessages.getOrElse(x, Nil())) &&
        messages.getOrElse((x._2,x._2), Nil()) == newMessages.getOrElse((x._2,x._2), Nil()) &&
        collectWWs(messages.getOrElse((x._2,x._2), Nil())) == collectWWs(newMessages.getOrElse((x._2,x._2), Nil())) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectWWs(newMessages.getOrElse((x._2, x._2), Nil()))).isEmpty &&
        addWWProp9(messages, channels, id, m) &&
        prop9(newMessages, channels) &&
        true
    }
  
  }holds
  
  def removeWUProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop6(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteUser(s,i), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(WriteUser(s,i),ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    theorem2(c, channels, WriteUser(s,i), messages) &&
    collectWUsList(messages, channels).contains(WriteUser(s,i)) &&
    !collectWWsList(messages, channels).contains(WriteUser(s,i)) &&
    removeCollectWW(messages, channels, c) &&
    !collectWWsList(newMessages, channels).contains(WriteUser(s,i))
  
  }holds
  
  def addWSProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      {
        m match {
          case WriteSystem(s,i,_,_) =>  
            !collectWWs(messages.getOrElse((c._2, c._2), Nil())).contains(WriteUser(s,i))
          case _ => false
        }
      } 
    )
  
    val newMessages = add(messages, c, m)
    val WriteSystem(s,i,_,_) = m
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == c._2) => 
        addCollect3One(messages.getOrElse((x._2,x._2), Nil()),m) &&
        collectWWs(newMessages.getOrElse((x._2, x._2), Nil())) == collectWWs(messages.getOrElse((x._2, x._2), Nil())) &&
        !collectWWs(messages.getOrElse((x._2, x._2), Nil())).contains(WriteUser(s,i)) &&
        !collectWWs(newMessages.getOrElse((x._2, x._2), Nil())).contains(WriteUser(s,i)) &&
        addCollectOneWS(messages.getOrElse(x, Nil()), m) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectWWs(newMessages.getOrElse((x._2, x._2), Nil()))).isEmpty &&
        addWSProp9(messages, xs, c, m) &&
        prop9(newMessages, xs) &&
        true
        
      case Cons(x,xs) => 
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        messages.getOrElse((x._2,x._2), Nil()) == newMessages.getOrElse((x._2,x._2), Nil()) &&
        (collectWSs(newMessages.getOrElse(x, Nil())) & collectWWs(newMessages.getOrElse((x._2, x._2), Nil()))).isEmpty &&
        addWSProp9(messages, xs, c, m) &&
        prop9(newMessages, xs) &&
        true
        
    }
  
  }holds
 
 def addOtherProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      {
        m match {
          case WriteSystem(s,i,_,_) =>  false
          case WriteWaiting(s,i,_,_) => false
          case _ => true
        }
      } 
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        addCollect3One(messages.getOrElse((x._2,x._2), Nil()),m) &&
        addCollect2One(messages.getOrElse(x, Nil()),m) &&
        addOtherProp9(messages, xs, c, m) &&
        prop9(newMessages, channels)
    }
    
  }holds
  
  def removeAllProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop9(messages, channels) && 
      !messages.getOrElse(c, Nil()).isEmpty
    )
    val Cons(_,ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        removeCollectWS(messages, channels, c) &&
        removeCollectWW(messages, channels, c) &&
        removeAllProp9(messages, channels, c) &&
        prop9(newMessages, channels)
    }
  
  }holds
  
  def removeWWProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    id: ActorId
  ): Boolean = {
    require(
      prop9(messages, channels) &&
      {
        messages.getOrElse((id,id), Nil()) match {
          case Cons(WriteWaiting(s,i,_,_),xs) => true
          case _ => false
        }
      }
    )
    val Cons(WriteWaiting(s,i,_,_),ds) = messages.getOrElse((id,id), Nil())
    val newMessages = messages.updated((id,id), ds)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) =>
        collectWWs(messages.getOrElse((id,id), Nil())).contains(WriteUser(s,i)) &&
        !collectWSs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        removeCollectWS(messages, channels, (id,id))&&        
        removeWWProp9(messages, xs, id) &&
        !collectNeighbour(id, channels, newMessages).contains(WriteUser(s,i))
      case Cons(x,xs) =>  
        removeWWProp9(messages, xs, id) &&
        !collectNeighbour(id, channels, newMessages).contains(WriteUser(s,i))
    }
  
  }holds
  
  def removeProp9(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop9(messages, channels) && 
      prop6(messages, channels) &&
      prop5(messages, channels) &&
      prop7(channels, messages) &&
      !messages.getOrElse(c, Nil()).isEmpty &&
      channels.contains(c)
    )
    val Cons(m,ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    m match {
      case WriteSystem(s,i,_,_) =>
        removeAllProp9(messages, channels, c) &&
        removeWSprop9_2(messages, channels, c)
      case WriteUser(s,i) =>
        removeAllProp9(messages, channels, c) &&
        removeWUProp9(messages, channels, c)
      case WriteWaiting(s,i,_,_) if (c._1 == c._2) => 
        removeAllProp9(messages, channels, c) &&
        removeWWProp9(messages, channels, c._2)
      case _ =>
        removeAllProp9(messages, channels, c)
    }
  }holds

  def collectOtherActorProp9(
    otherActor: List[ActorId],
    messages: Map[(ActorId,ActorId),List[Message]],
    m: Message
  ): Boolean = {
    otherActor match {
      case Nil() => true
      case Cons(x,xs) => 
        !collectWWs(messages.getOrElse((x, x), Nil())).contains(m) &&
        collectOtherActorProp9(xs, messages, m)
    }
  }
  
  def lemmaReceiveProp9(
    otherActor: List[ActorId],
    messages: Map[(ActorId,ActorId),List[Message]],
    m: Message
  ): Boolean = {
    require(
      areInChannelsBis(otherActor) &&
      !collectWWsList(messages, channels).contains(m)
    )
    
    otherActor match {
      case Nil() => true
      case Cons(x,xs) =>
        collectListToOne((x,x), channels, messages, m) &&
        !collectWWs(messages.getOrElse((x,x), Nil())).contains(m) &&
        lemmaReceiveProp9(xs, messages, m) &&
        collectOtherActorProp9(otherActor, messages, m)
    }
  }holds
  
  def collectListToOne(
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    m: Message
  ): Boolean = {
    require(
      !collectWWsList(messages, channels).contains(m) &&
      channels.contains(c)
    )
    
    channels match {
      case Cons(x,xs) if (x==c) => 
        !collectWWs(messages.getOrElse(c, Nil())).contains(m)
      case Cons(x,xs) => 
        collectListToOne(c, xs, messages, m) &&
        !collectWWs(messages.getOrElse(c, Nil())).contains(m)
    }
  
  }holds
  
  def broadcastAckPreInductProp9(
    myId : ActorId,
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message
  ): Boolean = {
    require(
      distinctElements[ActorId](otherActor) &&
      {
        m match {
          case WriteSystem(s,i,_idM,h) => 
            collectOtherActorProp9(otherActor, messages, WriteUser(s,i))
          case _ => false
        }
      } &&
      !otherActor.isEmpty
    )
    val WriteSystem(s,i,idM,h) = m
    val Cons(id,_) = otherActor
    val newMessages = add(messages, (myId,id), m) 
    
    otherActor match {
      case Cons(x,Nil()) => true
      case Cons(x,Cons(y,ys)) => 
        x == id &&
        x != y &&
        (y,y) != (myId,id) &&
        messages.getOrElse((y,y), Nil()) == newMessages.getOrElse((y,y), Nil()) &&
        !collectWWs(messages.getOrElse((y, y), Nil())).contains(WriteUser(s,i)) &&
        !collectWWs(newMessages.getOrElse((y, y), Nil())).contains(WriteUser(s,i)) &&
        broadcastAckPreInductProp9(myId, Cons(x,ys), messages, m) &&
        collectOtherActorProp9(Cons(y,ys), newMessages, WriteUser(s,i)) &&
        true
    }
    
  }holds
  
  def initProp9(
    messages: Map[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(collectWSsList(messages, channels).isEmpty)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWSs(messages.getOrElse(x, Nil())).isEmpty &&
        initProp9(messages, xs) &&
        prop9(messages, channels)
    }
  }holds
}
