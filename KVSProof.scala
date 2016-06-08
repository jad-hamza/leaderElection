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
  
  def inChannels(net: VerifiedNetwork, id1:ActorId, id2:ActorId) = {
    require(validId(net,id1) && validId(net,id2))
    channels.contains((id1,id2))
  }holds
 
  def getmessages(ids: (ActorId,ActorId)): List[Message] = Nil()
  
  val init_messages = MMap(getmessages)
  
  def makeNetwork(p: Parameter) = {
    
    def states(id: ActorId): State = {
      id match {
        case ActorIdSys(x) => CommonState(MMap( (x: Variable) => 0 ), Set() ) 
        case ActorIdUser(x) => UserState(Nil(),0)
      }
    }
    
    def getActor(id: ActorId): Actor = id match {
      case ActorIdSys(x) => if (x == 1) {SystemActor(a1)}
			else {
			  if (x == 2) {SystemActor(a2)}
			  else {
			    SystemActor(a3)
			  }
			}
      case ActorIdUser(x) => UserActor(a4)
    }

    VerifiedNetwork(Variables(List(Variable(1))),
		MMap(states), 
		init_messages,
		MMap(getActor))
  }ensuring(res => writeEmpty(res.states) && networkInvariant(res.param,res.states,res.messages,res.getActor))

  
  def validParam(p: Parameter) = true
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    messages.getOrElse((a4,a4), Nil()).isEmpty &&
    getActor(a1) == SystemActor(a1) &&
    getActor(a2) == SystemActor(a2) &&
    getActor(a3) == SystemActor(a3) &&
    getActor(a4) == UserActor(a4) && 
    WriteHistory(messages, states) 
  }
  
  
  //basic functions
  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]) = true
    
  def userActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    require(networkInvariant(net.param, net.states, net.messages, net.getActor) && 
    {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }})
    val UserState(userHistory,c) = net.states(a4)

    val myId = receiver.myId

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i,idM), CommonState(mem,h)) =>true
//         check(userHistory.contains((idM,Set())))&&
//             (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a1)) &&
//             (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a2)) &&
//             (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a3))

      case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) => true
//        ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,h), myId, myId)
    
      case (id,WriteSystem(s,i,idM,hs), CommonState(mem,h)) => true
//        ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,h), myId, myId)

      case (id,Read(s), CommonState(mem,h)) => true
//        if (id == a4) {
//          ajoutCheckWriteForAll(channels, net.messages, userHistory, Value(mem(s)), myId, id)
//        }
//        else true

      case _ => true
    }
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    networkInvariant(net.param, net.states, net.messages, net.getActor) /*{
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }} &&*/ //(
//     a match {
//       case UserActor(_) => userActorReceivePre(a, sender, m)
//       case SystemActor(_) => systemActorReceivePre(a, sender, m)
//     })
  }
  
  def theorem(net: VerifiedNetwork, m: Message) = {
    require(networkInvariant(net.param,net.states,net.messages,net.getActor))
    val messages2 = net.messages.updated((a1,a2),net.messages(a1,a2) :+ m)
    networkInvariant(net.param,net.states,messages2,net.getActor)
  }holds
  
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
              inChannels(n, sender,receiver)&&
              inUserHistory(sender, receiver, n.messages, channels, h)&&
              checkWrite(sms, h)&&
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
    val newHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])] = Cons(((a4,c),Set()), h)
    val newStates = net.states.updated(a4,UserState(newHistory,c+1))
    val messages = net.messages.getOrElse((a4,a1), Nil())
    val newMessages = net.messages.updated((a4,a1),messages:+WriteUser(Variable(1),1,(a4,c)))
    
    ajoutUserCheckWriteForAll(channels, net.messages, h, ((a4,c),Set())) &&
    networkInvariant(net.param, newStates, net.messages, net.getActor) &&
    ajoutCheckWriteForAll(channels, net.messages, newHistory, WriteUser(Variable(1), 1, (a4,c)), a4, a1) &&  
    networkInvariant(net.param, newStates, newMessages, net.getActor) &&
true
    }
  }
  
//   def inUserHistoryAll(
//     list: List[(ActorId,ActorId)],
//     messages: MMap[(ActorId,ActorId),List[Message]],
//     states: MMap[ActorId, State]): Boolean = {
//     require(WriteHistory(messages,states))
//     list match {
//       case Nil() => true
//       case Cons(x,xs) => inUserHistory(x,messages,states) && inUserHistoryAll(xs,messages,states)
//     }
//   }
  
  def inUserHistory(
    sender: ActorId, 
    receiver: ActorId, 
    messages: MMap[(ActorId,ActorId),List[Message]],
    channel: List[(ActorId,ActorId)],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]
    ): Boolean = {
    require(checkWriteForAll(channel, messages, userHistory) && channel.contains((sender,receiver)))
    
    val message = messages((sender,receiver))
    channel match {
      case Cons(x,xs) if (x==(sender,receiver)) => checkWrite(message, userHistory)
      case Cons(x,xs) => inUserHistory(sender,receiver,messages,xs, userHistory) && checkWrite(message,userHistory)
    }
  }holds
  
  def writeEmpty(states:MMap[ActorId, State]) = {
    require(states(a4) match{
      case UserState(x,v) => true
      case _ => false
    })
    val UserState(x,v) = states(a4)
    checkWriteForAllEmpty(channels, x) &&
    WriteHistory(init_messages, states)
  }holds
  
  @induct
  def checkWriteForAllEmpty(
    list: List[(ActorId,ActorId)],
    userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]): Boolean = {
    checkWriteForAll(list, init_messages,userHistory)
  }holds

  //function to prove WriteHistory
  def checkWrite(l: List[Message], userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(y,v,idM) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case WriteSystem(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case WriteWaiting(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case _ => checkWrite(q, userHistory)
        }
    }
  }

  def checkWrite2(l: List[Message], userHistory: List[(ActorId,BigInt)]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(y,v,idM) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case WriteSystem(y,v,idM,h) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case WriteWaiting(y,v,idM,h) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case _ => checkWrite2(q, userHistory)
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
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    checkWrite(l :+ m, userHistory)

  } holds

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
    m: Message, a1: ActorId, a2: ActorId): Boolean = {
    require {
      checkWriteForAll(list, messages, userHistory) && (
        m match {
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
          case _ => true
        })
    }

    val ll = messages.getOrElse((a1,a2), Nil())
    val newMessages = messages.updated((a1,a2), ll :+ m)
    
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
  
  
  
  
  
  
   //functions to prove tableHistory
  def tableHistory(states: MMap[ActorId, State]): Boolean = {    
    states(a4) match {
      case UserState(userHistory,c) =>
        tableHistoryOne(a1,states(a1),userHistory) &&
        tableHistoryOne(a2,states(a2),userHistory) &&
        tableHistoryOne(a3,states(a3),userHistory)
      case _ => false
    }
  }
  
  def tableHistoryOne(a: ActorId, state: State, userHistory: List[((ActorId,BigInt),Set[(ActorId,BigInt)])]): Boolean = {
    true
  }
  
}
