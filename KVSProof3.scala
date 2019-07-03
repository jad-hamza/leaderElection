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

object ProtocolProof3 {
  import Protocol._
  import PrettyPrinting._
  import ProtocolProof._
  import ProtocolProof2._
  
  
// property 10
// less than two WW
  def prop10(
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId,ActorId),List[Message]],
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
    messages: Map[(ActorId, ActorId), List[Message]],
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
 




//property 8

  def prop8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
  
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        prop8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState())) &&
        prop8(messages, states, xs)
    }
    
  }
  
  def prop8One(
    list: List[Message], 
    state: State
  ): Boolean = {
    
    state match {
      case CommonState(mem,h) =>
        list match {
          case Nil() => true
          case Cons(m,xs) => 
            m match {
              case WriteSystem(s,i,_,_) => 
                !h.contains((true,s,i)) &&
                prop8One(xs, state)
              case _ => 
                prop8One(xs, state)
            }
        }
      case _ => true
    }
  }
  
  def addOtherProp8(
    messages: Map[(ActorId,ActorId),List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      {
        m match {
          case WriteSystem(_,_,_,_) => false
          case _ => true
        }
      }
    )
    val newMessages = add(messages, c, m)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        addOtherProp8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState()), m) &&
        addOtherProp8(messages, states, xs, c, m) &&
        prop8(newMessages, states, channels)
      case Cons(x, xs) => 
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        addOtherProp8(messages, states, xs, c, m) &&
        prop8(newMessages, states, channels)
    }
  
  }holds
  
  def addOtherProp8One(
    list: List[Message], 
    state: State, 
    m: Message
  ): Boolean = {
    require(
      m match {
        case WriteSystem(_,_,_,_) => false
        case _ => 
          prop8One(list, state)
      }
    )

    state match {
      case CommonState(mem,h) => 
        list match {
          case Nil() => prop8One(list :+ m, state)
          case Cons(x,xs) =>  
            addOtherProp8One(xs, state, m) &&
            prop8One(list :+ m, state)
        }
      case _ => true
    }

  }holds
  
  def removeWUProp8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)], 
    actors: List[ActorId],
    c: (ActorId, ActorId) 
  ): Boolean = {
    require(
      prop4(messages, states, channels, actors) &&
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
    
    channels match {
      case Cons(x,xs) if (x == c) => 
        !allHistoriesContainsAux(s, i, actors, states)
      case Cons(x,xs) =>
        removeWUProp8(messages, states, xs, actors, c) &&
        !allHistoriesContainsAux(s, i, actors, states)
    }
  
  }holds
  
  def removeAllProp8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId) 
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )
    val Cons(m,ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        prop8One(newMessages.getOrElse(c, Nil()), states.getOrElse(x._2, BadState())) &&
        removeAllProp8(messages, states, xs, c) &&
        prop8(newMessages, states, channels) &&
        true
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        removeAllProp8(messages, states, xs, c) &&
        prop8(newMessages, states, channels) &&
        true
    }
  
  }holds
  
  def removeProp8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)],
    actors: List[ActorId],
    c: (ActorId, ActorId) 
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty &&
      prop4(messages, states, channels, actors) &&
      channels.contains(c)
    )
    val Cons(m,ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)
    
    m match {
      case WriteUser(s,i) => 
        removeAllProp8(messages, states, channels, c) &&
        removeWUProp8(messages, states, channels, actors, c)
      case _ =>
        removeAllProp8(messages, states, channels, c)
    }
  
  
  }holds
  
  def leMaprop8(
    s: Variable,
    i: BigInt, 
    states: Map[ActorId, State],
    actors: List[ActorId],
    id: ActorId
  ): Boolean = {
    require(
      !allHistoriesContainsAux(s,i,actors, states) &&
      actors.contains(id)
    )
  
    actors match {
      case Cons(x,xs) if (x == id) => 
        states.getOrElse(id, BadState()) match {
          case CommonState(mem,h) =>
            !h.contains((true, s, i))
          case _ =>
            true
        }
      case Cons(x,xs) =>
        leMaprop8(s,i,states,xs,id) &&
        {
          states.getOrElse(id, BadState()) match {
            case CommonState(mem,h) =>
              !h.contains((true, s, i))
            case _ =>
              true
          }
        }
    }
  }holds
  
  def addWSProp8(
    messages: Map[(ActorId,ActorId),List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)],
    c: (ActorId,ActorId),
    m: Message,
    actors: List[ActorId]
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      actors.contains(c._2) &&
      {
        m match {
          case WriteSystem(s,i,_,_) => 
            !allHistoriesContainsAux(s,i,actors, states)
          case _ => false
        }
      }
    )
    val newMessages = add(messages, c, m)
    val WriteSystem(s,i,_,_) = m
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == c) => 
        leMaprop8(s,i,states, actors, c._2) &&
        addWSProp8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState()), m) &&
        prop8One(newMessages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState())) &&
        addWSProp8(messages, states, xs, c, m, actors) &&
        prop8(newMessages, states, channels)
      case Cons(x,xs) => 
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        addWSProp8(messages, states, xs, c, m, actors) &&
        prop8(newMessages, states, channels)
    }
    
  }holds
  
  def addWSProp8One(
    list: List[Message], 
    state: State, 
    m: Message
  ): Boolean = {
    require(
      prop8One(list, state) &&
      {
        m match {
          case WriteSystem(s,i,_,_) => 
            state match {
              case CommonState(mem,h) =>
                !h.contains((true, s, i))
              case _ =>
                true
            }
          case _ => false
        }
      }
    )
    
    state match {
      case CommonState(mem,h) => 
        list match {
          case Nil() => prop8One(list :+ m, state)
          case Cons(x,xs) =>
            addWSProp8One(xs, state, m) &&
            prop8One(list :+ m, state)
        }
      case _ =>
        true
    }
  
  }holds
  
  def initProp8(
   messages: Map[(ActorId, ActorId), List[Message]],
   channels: List[(ActorId, ActorId)], 
   states: Map[ActorId, State]
  ): Boolean = {
    require(
      collectWSsList(messages, channels).isEmpty
    )
    
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        collectWSs(messages.getOrElse(x, Nil())).isEmpty &&
        initProp8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState())) &&
        initProp8(messages, xs, states) &&
        prop8(messages, states, channels)
    }
  }holds
  
  def initProp8One(
    list: List[Message],
    state: State
  ): Boolean = {
    require(
      collectWSs(list).isEmpty
    )
  
    state match {
      case CommonState(mem,h) =>
        list match {
          case Nil() => true
          case Cons(m,xs) => 
            m match {
              case WriteSystem(s,i,_,_) => false
              case _ => 
                initProp8One(xs, state) &&
                prop8One(list, state)
            }
        }
      case _ => true
    }   
  
  }holds
  
  def updateStateUserProp8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)], 
    id: ActorId,
    newState: State
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      {
        newState match {
          case UserState(_,_) => true
          case _ => false
        }
      }
    )
    val newStates = states.updated(id, newState)
    
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) => 
        prop8One(messages.getOrElse(x, Nil()), newState) &&
        updateStateUserProp8(messages, states, xs, id, newState) &&
        prop8(messages, newStates, channels)
      case Cons(x,xs) =>
        states.getOrElse(x._2, BadState()) == newStates.getOrElse(x._2, BadState()) &&
        updateStateUserProp8(messages, states, xs, id, newState) &&
        prop8(messages, newStates, channels)
    }
  
  }holds
  
  def updateStateSystemProp8(
    messages: Map[(ActorId, ActorId), List[Message]],
    states: Map[ActorId, State],
    channels: List[(ActorId, ActorId)], 
    id: ActorId,
    s: Variable, 
    i: BigInt
  ): Boolean = {
    require(
      prop8(messages, states, channels) &&
      !collectNeighbour(id, channels, messages).contains(WriteUser(s,i)) &&
      {
        states.getOrElse(id, BadState()) match {
          case CommonState(mem,h) => true
          case _ => false
        }
      }
    )
    val CommonState(mem,h) = states.getOrElse(id, BadState())
    val newState = CommonState(mem.updated(s,i),h++Set((true,s,i)))
    val newStates = states.updated(id, newState)
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) =>
        !collectWSs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
        updateStateSystemProp8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState()), s, i) &&
        prop8One(messages.getOrElse(x, Nil()), newStates.getOrElse(x._2, BadState())) &&
        updateStateSystemProp8(messages, states, xs, id, s, i) &&
        prop8(messages, newStates, channels)
        
      case Cons(x,xs) =>  
        states.getOrElse(x._2, BadState()) == newStates.getOrElse(x._2, BadState()) &&
        updateStateSystemProp8(messages, states, xs, id, s, i) &&
        prop8(messages, newStates, channels)
    }
  
  }holds
  
  def updateStateSystemProp8One(
    list: List[Message], 
    state: State, 
    s: Variable, 
    i: BigInt
  ): Boolean = {
    require(
      prop8One(list, state) &&
      !collectWSs(list).contains(WriteUser(s,i)) &&
      {
        state match {
          case CommonState(mem,h) => true
          case _ => false
        }
      }
    )
    val CommonState(mem,h) = state
    val newState = CommonState(mem.updated(s,i),h++Set((true,s,i)))
    
    state match {
      case CommonState(mem,h) =>
        list match {
          case Nil() => true
          case Cons(WriteSystem(x,v,_,_), xs) if ((x,v) == (s,i)) => 
            false
          case Cons(WriteSystem(x,v,_,_), xs) =>
            !(h ++Set((true, s,i))).contains((true,x,v)) &&
            updateStateSystemProp8One(xs, state, s, i) &&
            prop8One(list, newState)
          case Cons(x,xs) => 
            updateStateSystemProp8One(xs, state, s, i) &&
            prop8One(list, newState)
        }
      case _ => true
    }
  
  }holds
  
  def leMaprop8_2(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    id: ActorId,
    m: Message
  ): Boolean = {
    require(
      !collectWSsList(messages, channels).contains(m)
    )
  
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x._2 == id) =>
        !collectWSs(messages.getOrElse(x, Nil())).contains(m) &&
        leMaprop8_2(messages, xs, id, m) &&
        !collectNeighbour(id, channels, messages).contains(m)
      case Cons(x,xs) =>  
        leMaprop8_2(messages, xs, id, m) &&
        !collectNeighbour(id, channels, messages).contains(m)
    }
  
  }holds
  
  def subLemma(
    s: Variable, 
    i: BigInt,
    actors: List[ActorId], 
    states: Map[ActorId, State], 
    id: ActorId
  ): Boolean = {
    require(
      !allHistoriesContainsAux(s, i, actors, states) &&
      actors.contains(id)
    )
    
    actors match {
      case Cons(x,xs) if (x == id) =>   
        states.getOrElse(id, BadState()) match {
          case CommonState(mem, h) =>
            !h.contains((true,s,i))
          case _ => true
        }
      case Cons(x,xs) =>
        subLemma(s,i,xs,states,id) &&
        {
        states.getOrElse(id, BadState()) match {
          case CommonState(mem, h) =>
            !h.contains((true,s,i))
          case _ => true
        }
        }
    }
    
  }holds
  
  def leMaprop8_3(
    s: Variable, 
    i: BigInt,
    otherActor: List[ActorId], 
    actors: List[ActorId], 
    states: Map[ActorId, State], 
    newState: State, 
    id: ActorId
  ): Boolean = {
    require(
      !allHistoriesContainsAux(s, i, actors, states) &&
      subsetOf(otherActor, actors) &&
      !otherActor.contains(id)
    )
    val newStates = states.updated(id, newState)
    
    otherActor match {
      case Nil() => true
      case Cons(x, xs) => 
        subLemma(s,i,actors,states,x) &&
        newStates.getOrElse(x, BadState()) == states.getOrElse(x, BadState()) &&
        leMaprop8_3(s,i,xs,actors,states,newState,id) &&
        !allHistoriesContainsAux(s, i, otherActor, newStates)
    }
  
  }holds
  
  





  def collectIDs(
    channels: List[(ActorId, ActorId)],
    states: Map[ActorId, State],
    s: Variable, 
    i: BigInt
  ): Set[ActorId] = {
    channels match {
      case Nil() => Set()
      case Cons(x,xs) => 
        states.getOrElse(x._2, BadState()) match {
          case CommonState(mem,h) if (h.contains((true,s,i))) =>
            collectIDs(xs, states, s, i) ++Set(x._2)
          case _ => 
            collectIDs(xs, states, s, i)
        }
    }
  }
  
//   def removeWUProp8(
//     messages: Map[(ActorId,ActorId),List[Message]],
//     channels: List[(ActorId,ActorId)],
//     states: Map[ActorId, State],
//     c: (ActorId, ActorId)
//   ): Boolean = {
//     require(
//       uniqueWriteUser(messages, channels) &&
//       prop4Aux(messages, states, channels) &&
//       {
//         messages.getOrElse(c, Nil()) match {
//           case Cons(x@WriteUser(s,i), xs) => 
//             true
//           case _ => false
//         }
//       } &&
//       channels.contains(c)
//     )
//     val Cons(WriteUser(s,i),ds) = messages.getOrElse(c, Nil())
//     
//     channels match {
//       case Cons(x,xs) if (x == c) => 
//         !allHistoriesContains(s, i, channels, states) &&
//         leMaprop8(s,i,channels, states) &&
//         collectIDs(channels, states, s, i).isEmpty
//       case Cons(x,xs) => 
//         theorem2(c, xs, WriteUser(s,i), messages) && 
//         collectWUsList(messages, xs).contains(WriteUser(s,i)) &&
//         !collectWUs(messages.getOrElse(x, Nil())).contains(WriteUser(s,i)) &&
//         removeWUProp8(messages, xs, states, c) &&
//         collectIDs(channels, states, s, i).isEmpty &&
//         true
//     }
//   
//   }holds
//   
//   
//   
//   def otherActorProp8(
//     channels: List[(ActorId, ActorId)],
//     messages: Map[(ActorId,ActorId),List[Message]],
//     otherActor: List[ActorId],
//     m: Message
//   ): Boolean = {
//     otherActor match {
//       case Nil() => true
//       case Cons(x,xs) =>
//         !collectNeighbour(x, channels, messages).contains(m) &&
//         otherActorProp8(channels, messages, xs, m)
//     }
//   }
//   
//   def broadcastProp8(
//     channels: List[(ActorId, ActorId)],
//     messages: Map[(ActorId,ActorId),List[Message]],
//     otherActor: List[ActorId],
//     m: Message
//   ): Boolean = {
//     require(
//       !collectWSsList(messages, channels).contains(m)
//     )
//     
//     otherActor match {
//       case Nil() => true
//       case Cons(x,xs) => 
//         theoremProp8(channels, messages, x, m) &&
//         !collectNeighbour(x, channels, messages).contains(m) &&
//         broadcastProp8(channels, messages, xs, m) &&
//         otherActorProp8(channels, messages, otherActor, m)
//     }
//     
//   }holds
//   
//   def updateBroadcastProp8(
//     id: ActorId,
//     channels: List[(ActorId, ActorId)],
//     messages: Map[(ActorId,ActorId),List[Message]],
//     otherActor: List[ActorId],
//     m: Message
//   ): Boolean = {
//     require(
//       m match {
//         case WriteSystem(s,i,idM,h) => 
//           otherActorProp8(channels, messages, otherActor, WriteUser(s,i)) &&
//           distinctElements[ActorId](otherActor)
//         case _ => false
//       }
//     )
//     val WriteSystem(s,i,idM,h) = m
//     
//     otherActor match {
//       case Nil() => true
//       case Cons(x,Nil()) => 
//         otherActorProp8(channels, add(messages, (id,x), m), Nil(), WriteUser(s,i))
//       case Cons(x, Cons(y,ys)) => 
//         addCollectNeighbourWSOther(channels, messages, y, (id,x), WriteUser(s,i), m) &&
//         !collectNeighbour(y, channels, add(messages, (id,x), m)).contains(WriteUser(s,i)) &&
//         updateBroadcastProp8(id, channels, messages, Cons(x,ys), m) &&
//         otherActorProp8(channels, add(messages, (id,x), m), Cons(y,ys), WriteUser(s,i)) &&
//         true
//     }    
// 
//   }holds
//   
//   def prop8(
//     messages: Map[(ActorId, ActorId), List[Message]],
//     states: Map[ActorId, State],
//     channels: List[(ActorId, ActorId)]
//   ): Boolean = {
//   
//     channels match {
//       case Nil() => true
//       case Cons(x,xs) => 
//         prop8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState())) &&
//         prop8(messages, states, xs)
//     }
//     
//   }
//   
//   def prop8One(
//     list: List[Message], 
//     state: State
//   ): Boolean = {
//     
//     list match {
//       case Nil() => true
//       case Cons(m,xs) => 
//         m match {
//           case WriteSystem(s,i,_,_) => 
//             state match {
//               case CommonState(mem,h) =>
//                 !h.contains((true,s,i)) &&
//                 prop8One(xs, state)
//               case _ => 
//                 prop8One(xs, state)
//             }
//           case _ => 
//             prop8One(xs, state)
//         }
//     }
//   }
//   

//   

//  
//   def addWSProp8(
//     messages: Map[(ActorId,ActorId),List[Message]],
//     states: Map[ActorId, State],
//     channels: List[(ActorId, ActorId)],
//     c: (ActorId,ActorId),
//     m: Message
//   ): Boolean = {
//     require(
//       prop8(messages, states, channels) &&
//       {
//         m match {
//           case WriteSystem(s,i,_,_) => 
//             states.getOrElse(c._2, BadState()) match {
//               case CommonState(mem,h) =>
//                 !h.contains((true,s,i))
//               case _ => true
//             }
//           case _ => false
//         }
//       }
//     )
//     val newMessages = add(messages, c, m)
//     
//     channels match {
//       case Nil() => true
//       case Cons(x,xs) if (x == c) => 
//         addWSProp8One(messages.getOrElse(x, Nil()), states.getOrElse(x._2, BadState()), m) &&
//         addWSProp8(messages, states, xs, c, m) &&
//         prop8(newMessages, states, channels)
//       case Cons(x, xs) => 
//         messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
//         addWSProp8(messages, states, xs, c, m) &&
//         prop8(newMessages, states, channels)
//     }
//     
//   }holds
//   
//   def addWSProp8One(
//     list: List[Message], 
//     state: State, 
//     m: Message
//   ): Boolean = {
//     require(
//       m match {
//         case WriteSystem(s,i,_,_) => 
//           state match {
//             case CommonState(mem,h) => 
//               prop8One(list, state) &&
//               !h.contains((true,s,i))
//             case _ =>   
//               prop8One(list, state)
//           }
//         case _ => false
//       }
//     )
// 
//     list match {
//       case Nil() => prop8One(list :+ m, state)
//       case Cons(x,xs) =>  
//         addWSProp8One(xs, state, m) &&
//         prop8One(list :+ m, state)
//     }
//     
//   }holds
}
