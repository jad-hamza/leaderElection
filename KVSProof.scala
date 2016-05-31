package distribution


import FifoNetwork._
import Networking._

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
  
  // if there is a Write in a channel then there is the correspondant operation in the history of the User
  def WriteHistory(messages: MMap[(ActorId,ActorId),List[Message]], states:MMap[ActorId, State]): Boolean = {
    require(states.contains(a1) && states.contains(a2) && states.contains(a3) && states.contains(a4))
    
    def checkWrite(l: List[Message], userHistory: List[(String,BigInt,Set[(String,BigInt)])]):Boolean = {
      l match {
        case Nil() => true
        case x::q => 
          x match {
            case WriteUser(x,v) => userHistory.contains((x,v,Set())) && checkWrite(q, userHistory)
            //case WriteSystem(x,v,h) =>  checkWrite(q, userHistory)
            //case WriteWaiting(x,v,h) =>  checkWrite(q, userHistory)
            case _ => checkWrite(q, userHistory)
          }
      }
    }
    
    def loop(list: List[(ActorId,ActorId)], userHistory: List[(String,BigInt,Set[(String,BigInt)])]): Boolean = {
      list match {
        case Nil() => true
        case (actor1,actor2)::q =>
          checkWrite(messages.getOrElse((actor1,actor2),Nil()), userHistory) && loop(q, userHistory)
      }
    }
    
    states(a4) match {
      case UserState(userHistory) =>
        loop(
          List(
            (a1,a1)//,(a1,a2),(a1,a3),(a1,a4),
            //(a2,a1),(a2,a2),(a2,a3),(a2,a4),
            //(a3,a1),(a3,a2),(a3,a3),(a3,a4),
            //(a4,a1),(a4,a2),(a4,a3),(a4,a4)
          ),
          userHistory
        )
      case _ => false
    }
  }
  
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
    
  def countingActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def checkingActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    true
  }
  
  def peekMessageEnsuresReceivePre(n: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    require(networkInvariant(n.param, n.states, n.messages, n.getActor) && validId(n,sender) && validId(n,receiver))
    val sms = n.messages.getOrElse((sender,receiver), Nil())
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = n.messages.updated((sender,receiver), xs);
        ((receiver == a4) ==> (sender == a1 || sender == a2 || sender == a3))
 
      case _ => 
        true
    }
  } holds
  
  
  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    true
  }
  
  
  def min(l: List[Message]): BigInt = {
    0
  }
  
  def max(l: List[Message]): BigInt = {
    0
  }
  

  def isSorted(l: List[Message]): Boolean = {
    true
  }
  
  def areDelivers(l: List[Message]): Boolean = {
    true
  }
  
  @induct 
  def appendDeliver(messages: List[Message], x: BigInt) = {
    true
  } holds
  
  def areIncrements(l: List[Message]): Boolean = {
    true
  }
  
  @induct 
  def appendIncrement(messages: List[Message]) = {
    true
  } holds

  
  @induct
  def appendItself(l: List[Message], j: BigInt) = {
    true
  } holds
  
  @induct
  def appendLarger(l: List[Message], j: BigInt, k: BigInt) = {
    true
  } holds
  
  @induct
  def appendSorted(l: List[Message], j: BigInt) = {
    true
  } holds
  
  
  @induct
  def smallestHead(j: BigInt, l: List[Message]) = {
    true
  } holds
}
