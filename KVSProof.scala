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
        case ActorIdSys(x) => Some(CommonState(MMap( (x: String) => (None[BigInt]) ), Set() ) )
        case ActorIdUser(x) => Some(UserState(Nil()))
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
    //checkMyChannel(a4,messages) 
    //checkMyChannel(a1,messages)
    //checkMyChannel(a2,messages)
    //checkMyChannel(a3,messages)
    WriteHistory(messages, states)
  }


  def checkWrite(l: List[Message], userHistory: List[(String,BigInt,Set[(String,BigInt)])]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(x,v) => userHistory.contains((x,v,Set())) && checkWrite(q, userHistory)
          //case WriteSystem(x,v,h) =>  checkWrite(q, userHistory)
          //case WriteWaiting(x,v,h) =>  checkWrite(q, userHistory)
          case _ => checkWrite(q, userHistory)
        }
    }
  }

  def checkWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[(String,BigInt,Set[(String,BigInt)])]): Boolean = {

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
      case UserState(userHistory) =>
        checkWriteForAll(
          channels,
          messages,
          userHistory
        )
      case _ => false
    }
  }

  @induct
  def ajoutCheckWrite(l: List[Message], m: Message, userHistory: List[(String,BigInt,Set[(String,BigInt)])]):Boolean = {
    require {
      checkWrite(l, userHistory) && (
        m match {
          case WriteUser(x,v) => userHistory.contains((x,v,Set()))
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
    userHistory: List[(String,BigInt,Set[(String,BigInt)])],
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
    userHistory: List[(String,BigInt,Set[(String,BigInt)])],
    t: (String,BigInt,Set[(String,BigInt)])
  ):Boolean = {
    require(checkWrite(l, userHistory))

    checkWrite(l, Cons(t, userHistory))

  } holds

  def ajoutUserCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[(String,BigInt,Set[(String,BigInt)])],
    t: (String,BigInt,Set[(String,BigInt)])
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
    userHistory: List[(String,BigInt,Set[(String,BigInt)])],
    m: Message, a1: ActorId, a2: ActorId): Boolean = {
    require {
      checkWriteForAll(list, messages, userHistory) && (
        m match {
          case WriteUser(x,v) => userHistory.contains((x,v,Set()))
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

  // nothing in the channel (a,a) except WriteWaiting messgaes
  //def checkMyChannel(a: ActorId, messages:MMap[(ActorId,ActorId),List[Message]]) = {
  //  val myChannel = messages.getOrElse((a,a), Nil());
    
  //  def checkMyChannelAux(l: List[Message]): Boolean = {
  //    l match {
  //      case Nil() => true
  //      case x::q => 
  //        x match {
  //          case WriteWaiting(x,v,h) => checkMyChannelAux(q)
  //          case _ => false
  //        } 
  //    }
  //  }
    
  //  checkMyChannelAux(myChannel)
//  }
  
  // there are no Read(s) messages in all channels leaving a
//  def noRead(a:ActorId, messages:MMap[(ActorId,ActorId),List[Message]]) = {
//    def noReadChannelAux(l:List[Message]):Boolean = {
//      l match {
//        case Nil() => true
//        case x::q => 
//          x match {
//            case Read(s) => false
//            case _ => noReadChannelAux(q)
//          }
//      }
//    }
    
//    def noReadChannel(act1:ActorId,act2:ActorId, messages:MMap[(ActorId,ActorId),List[Message]]) = {
//      noReadChannelAux(messages.getOrElse((act1,act2), Nil()))
//    }
//    
//    noReadChannel(a,a1,messages) && noReadChannel(a,a2,messages) && noReadChannel(a,a3,messages) && noReadChannel(a,a4,messages)
//  }
  
  
  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]) = true
    
  def userActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    val UserState(userHistory) = net.states(a4)

//    val SystemActor(myId) = receiver
    val myId = receiver.myId

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i), CommonState(mem,h)) => false
//        update(CommonState(mem.updated(s,i),h++Set((s,i))));
//        if(myId != a1){
//          !! (a1, WriteSystem(s,i,h))
//        };
//        if(myId != a2){
//          !! (a2, WriteSystem(s,i,h))
//        };
//        if(myId != a3){
//          !! (a3, WriteSystem(s,i,h))
//        };
//        !! (a4, AckUser(s,i,h))

      case (id, WriteSystem(s,i,hs), CommonState(mem,h)) => false
//        if (checkHistory(h,hs)) {
//          update(CommonState(mem.updated(s,i),h++Set((s,i))));
//        }
//        else {
//          !! (myId, WriteWaiting(s,i,hs))
//        }

      case (id, WriteWaiting(s,i,hs), CommonState(mem,h)) =>
        if (id != myId) {
//          update(BadState())
          true
        }
        else false
//        else { // I try to use the message as if it came from an other SystemUser
//          if (checkHistory(h,hs)) {
//            update(CommonState(mem.updated(s,i),h++Set((s,i))));
//          }
//          else { // I have not received enough messages, I send the message back to the Waiting List
//            !! (myId, WriteWaiting(s,i,hs))
//          }
//        }

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
    networkInvariant(net.param, net.states, net.messages, net.getActor) && (
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
            case UserState(h) =>
              removeCheckWriteForAll(channels, n.messages, h, sender, receiver) &&
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
      val UserState(h) = net.states(myId)
      ajoutUserCheckWriteForAll(channels, net.messages, h, ("1", 1, Set()))
    }
  }
  

}
