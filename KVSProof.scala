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

object ProtocolProof {
  import Protocol._
  import PrettyPrinting._
  
  def validId(net: VerifiedNetwork, id: ActorId) = {
    id == a1 || id == a2 || id == a3 || id == a4
  }
 
  
  
  def makeNetwork(p: Parameter) = {
    
    def states(id: ActorId): Option[State] = {
      id match {
        case ActorIdSys(x) => Some(CommonState(MMap( (x: Variable) => (None[BigInt]) ), Set() ) )
        case ActorIdUser(x) => Some(UserState(Nil(),0))
      }
    }
    
    def getActor(id: ActorId): Option[Actor] = id match {
      case ActorIdSys(x) => if (x == 1) {Some(SystemActor(a1))}
			else {
			  if (x == 2) {Some(SystemActor(a2))}
			  else {
			    Some(SystemActor(a3))
			  }
			}
      case ActorIdUser(x) => Some(UserActor(a4))
    }

    VerifiedNetwork(NoParam(), 
		MMap(states), 
		MMap(),
		MMap(getActor))
  }

  
  def validParam(p: Parameter) = true
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    states.contains(a1) &&
    states.contains(a2) &&
    states.contains(a3) &&
    states.contains(a4) && 
    getActor.contains(a1) &&
    getActor.contains(a2) &&  
    getActor.contains(a3) &&
    getActor.contains(a4) &&
    messages.getOrElse((a4,a4), Nil()).isEmpty &&
    getActor(a1) == SystemActor(a1) &&
    getActor(a2) == SystemActor(a2) &&
    getActor(a3) == SystemActor(a3) &&
    getActor(a4) == UserActor(a4) && 
    WriteHistory(messages, states) && 
    WriteSysHistory(messages, states)
  }


  def checkWrite(l: List[Message], userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case _ => checkWrite(q, userHistory)
        }
    }
  }

  def checkWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]): Boolean = {

    list match {
      case Nil() => true
      case Cons((actor1,actor2), q) =>
        checkWrite(messages.getOrElse((actor1,actor2),Nil()), userHistory) && checkWriteForAll(q, messages, userHistory)
    }
  }
  
  // if there is a Write in a channel then there is the corresponding operation in the history of the User
  def WriteHistory(messages: MMap[(ActorId,ActorId),List[Message]], states:MMap[ActorId, State]): Boolean = {
    require(states.contains(a1) && states.contains(a2) && states.contains(a3) && states.contains(a4))
    
    states(a4) match {
      case UserState(userHistory,c) =>
        checkWriteForAll(
          channels,
          messages,
          userHistory
        )
      case _ => false
    }
  }

  @induct
  def ajoutCheckWrite(l: List[Message], m: Message, userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]):Boolean = {
    require {
      checkWrite(l, userHistory) && (
        m match {
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    checkWrite(l :+ m, userHistory)

  } holds

//  def removeCheckWrite(l: List[Message], userHistory: List[(String,BigInt,Set[(String,BigInt)])]):Boolean = {
//    require(!l.isEmpty && checkWrite(l, userHistory))
//
//    val Cons(x, xs) = l
//
//    checkWrite(xs, userHistory)
//
//  } holds

  @induct
  def removeCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    a1: ActorId, a2: ActorId
  ):Boolean = {
    require(checkWriteForAll(list, messages, userHistory))

    val ll = messages.getOrElse((a1,a2),Nil())

    ll match {
      case Nil() => true
      case Cons(x,xs) => checkWriteForAll(list, messages.updated((a1,a2), xs), userHistory)
    }
//    list match {
//      case Nil() => checkWriteForAll(list, messages, Cons(t, userHistory))
//      case Cons((b1,b2),q) =>
//        ajoutUserCheckWrite(messages.getOrElse((b1,b2),Nil()), userHistory, t) &&
//        ajoutUserCheckWriteForAll(q, messages, userHistory, t) &&
//        checkWriteForAll(list, messages, Cons(t, userHistory))
//    }


  } holds

  @induct
  def ajoutUserCheckWrite(
    l: List[Message],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    t: ((ActorId,BigInt),Set[(ActorId,BigInt)])
  ):Boolean = {
    require(checkWrite(l, userHistory))

    checkWrite(l, Cons(t, userHistory))

  } holds

  def ajoutUserCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    t: ((ActorId,BigInt),Set[(ActorId,BigInt)])
  ):Boolean = {
    require(checkWriteForAll(list, messages, userHistory))

    list match {
      case Nil() => checkWriteForAll(list, messages, Cons(t, userHistory))
      case Cons((b1,b2),q) =>
        ajoutUserCheckWrite(messages.getOrElse((b1,b2),Nil()), userHistory, t) &&
        ajoutUserCheckWriteForAll(q, messages, userHistory, t) &&
        checkWriteForAll(list, messages, Cons(t, userHistory))
    }


  } holds

//  @induct
  def ajoutCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    m: Message, a1: ActorId, a2: ActorId)(implicit net: VerifiedNetwork): Boolean = {
    require {
      checkWriteForAll(list, messages, userHistory) && (
        m match {
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    val ll = messages.getOrElse((a1,a2), Nil())
    val newMessages = messages.updated((a1,a2), ll :+ m)
//    checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)


    list match {
      case Nil() => checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
      case Cons((b1,b2),q) =>
        if (a1 == b1 && a2 == b2)
          ajoutCheckWrite(ll, m, userHistory) &&
          ajoutCheckWriteForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
        else
          checkWrite(newMessages.getOrElse((b1,b2), Nil()), userHistory) &&
          ajoutCheckWriteForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
    }
  } holds

  
  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]) = true
    
  def userActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    require(networkInvariant(net.param, net.states, net.messages, net.getActor) && net.states.contains(a4) && net.states.contains(sender) && net.states.contains(receiver.myId))
    val UserState(userHistory,c) = net.states(a4)

//    val SystemActor(myId) = receiver
    val myId = receiver.myId

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i,idM), CommonState(mem,h)) =>
//        update(CommonState(mem.updated(s,i),h++Set((s,i))));
//        if(myId != a1){
            //checkWriteForAll(channels, net.messages, userHistory)&& //to easilycheck precondition of ajoutcheckWriteForAll
            ((myId != a1 && ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a1)) || (myId == a1)) &&
//          !! (a1, WriteSystem(s,i,h))
//        } &&
//        if(myId != a2){
            ((myId != a2 && ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a2)) || (myId == a2)) &&
//          !! (a2, WriteSystem(s,i,h))
//        };
//        if(myId != a3){
            ((myId != a3 && ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a3)) || (myId == a3))
//          !! (a3, WriteSystem(s,i,h))
//        };
//        !! (a4, AckUser(s,i,h))

      case (id,Read(s), CommonState(mem,h)) =>
        if (id == a4 && mem.contains(s)) {
          ajoutCheckWriteForAll(channels, net.messages, userHistory, Value(mem(s)), myId, id)
//          true
//          !! (id, Value(mem(s))) //cannot return None in default case
        }
        else true

      case _ => true
//        update(BadState())
    }
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    networkInvariant(net.param, net.states, net.messages, net.getActor)  && net.states.contains(sender) && net.states.contains(a.myId) && (
    m match {
        case WriteUser(x,v,idM) => WriteHistory(net.messages,net.states)
        case _ => true
    }) && (
    a match {
      case UserActor(_) => userActorReceivePre(a, sender, m)
      case SystemActor(_) => systemActorReceivePre(a, sender, m)
    })
  }
  
  def peekMessageEnsuresReceivePre(n: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    require(networkInvariant(n.param, n.states, n.messages, n.getActor) && validId(n,sender) && validId(n,receiver))
    val sms = n.messages.getOrElse((sender,receiver), Nil())
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = n.messages.updated((sender,receiver), xs);
        ((receiver == a4) ==> (sender == a1 || sender == a2 || sender == a3)) && {
          n.states(a4) match {
            case UserState(h,counter) =>
              removeCheckWriteForAll(channels, n.messages, h, sender, receiver) &&
              removeCheckWriteSysForAll(channels, n.messages, h, sender, receiver) &&
              networkInvariant(n.param, n.states, messages2, n.getActor)
            case _ => networkInvariant(n.param, n.states, messages2, n.getActor)
          }
        }
 
      case _ => 
        true
    }
  } holds



  def initPre(myId: ActorId, net: VerifiedNetwork) = {
    myId == a4 &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) && {
      val UserState(h,c) = net.states(myId)
      ajoutUserCheckWriteForAll(channels, net.messages, h, ((a4,1), Set())) &&
      ajoutUserCheckWriteSysForAll(channels, net.messages, h, ((a4,1), Set()))
    }
  }
  

  def WriteSysHistory(messages: MMap[(ActorId,ActorId),List[Message]], states:MMap[ActorId, State]): Boolean = {
    require(states.contains(a1) && states.contains(a2) && states.contains(a3) && states.contains(a4))
    
    states(a4) match {
      case UserState(userHistory,c) =>
        checkWriteSysForAll(
          channels,
          messages,
          userHistory
        )
      case _ => false
    }
  }
  
   def checkWriteSysForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]): Boolean = {

    list match {
      case Nil() => true
      case Cons((actor1,actor2), q) =>
        checkWriteSys(messages.getOrElse((actor1,actor2),Nil()), userHistory) && checkWriteSysForAll(q, messages, userHistory)
    }
  }
  
  def checkWriteSys(l: List[Message], userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set())) && checkWriteSys(q, userHistory)
          case _ => checkWriteSys(q, userHistory)
        }
    }
  }
  
  @induct
  def ajoutCheckWriteSys(l: List[Message], m: Message, userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]):Boolean = {
    require {
      checkWriteSys(l, userHistory) && (
        m match {
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    checkWriteSys(l :+ m, userHistory)

  } holds
  
  @induct
  def removeCheckWriteSysForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    a1: ActorId, a2: ActorId
  ):Boolean = {
    require(checkWriteSysForAll(list, messages, userHistory))

    val ll = messages.getOrElse((a1,a2),Nil())

    ll match {
      case Nil() => true
      case Cons(x,xs) => checkWriteSysForAll(list, messages.updated((a1,a2), xs), userHistory)
    }
  } holds
 
  @induct
  def ajoutUserCheckWriteSys(
    l: List[Message],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    t: ((ActorId,BigInt),Set[(ActorId,BigInt)])
  ):Boolean = {
    require(checkWriteSys(l, userHistory))

    checkWriteSys(l, Cons(t, userHistory))

  } holds

  def ajoutUserCheckWriteSysForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    t: ((ActorId,BigInt),Set[(ActorId,BigInt)])
  ):Boolean = {
    require(checkWriteSysForAll(list, messages, userHistory))

    list match {
      case Nil() => checkWriteSysForAll(list, messages, Cons(t, userHistory))
      case Cons((b1,b2),q) =>
        ajoutUserCheckWriteSys(messages.getOrElse((b1,b2),Nil()), userHistory, t) &&
        ajoutUserCheckWriteSysForAll(q, messages, userHistory, t) &&
        checkWriteSysForAll(list, messages, Cons(t, userHistory))
    }
  } holds
 
  def ajoutCheckWriteSysForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])],
    m: Message, a1: ActorId, a2: ActorId)(implicit net: VerifiedNetwork): Boolean = {
    require {
      checkWriteSysForAll(list, messages, userHistory) && (
        m match {
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    val ll = messages.getOrElse((a1,a2), Nil())
    val newMessages = messages.updated((a1,a2), ll :+ m)

    list match {
      case Nil() => checkWriteSysForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
      case Cons((b1,b2),q) =>
        if (a1 == b1 && a2 == b2)
          ajoutCheckWriteSys(ll, m, userHistory) &&
          ajoutCheckWriteSysForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteSysForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
        else
          checkWriteSys(newMessages.getOrElse((b1,b2), Nil()), userHistory) &&
          ajoutCheckWriteSysForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteSysForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
    }
  } holds
  
}
