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
        case ActorIdSys(x) => Some(CommonState(MMap( (x: String) => (None[BigInt]) ), Nil() ) )
        case ActorIdUser(x) => Some(UserState())
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
    consistency(states.apply(a1)) &&
    consistency(states.apply(a2)) &&
    consistency(states.apply(a3))
  }
  
  def consistency(state:State):Boolean = {
    state match {
      case BadState() => false
      case CommonState(mem,h) => (consistency1(h) && consistency2(h))
    }
  }
  
  def consistency1(history:List[(String,String,BigInt)]):Boolean = {
    history match {
      case Nil() => true
      case (action,variable,value)::q => 
        if (action == "read") {
          searchWrite(variable,value,q)
        }
        else {
          consistency1(q)
        }
     }
  }
  
  def searchWrite(variable:String, value:BigInt, history:List[(String,String,BigInt)]): Boolean = {
    history match {
      case Nil() => false
      case (action,x,v)::q => 
        if (action == "write" && x == variable && v == value) {
          true
        }
        else {
          searchWrite(variable, value, q)
        }
    }
  }
  
  def consistency2(history:List[(String,String,BigInt)]):Boolean = {
    history match {
      case Nil() => true
      case (action,variable,value)::q => 
        if (action == "read") {
          searchBadWrite(variable,value,q)
        }
        else {
          consistency2(q)
        }
    }
  }
  
  def searchBadWrite(variable:String, value:BigInt, history:List[(String,String,BigInt)]): Boolean = {
    history match {
      case Nil() => true
      case (action,x,v)::q => 
        if (action == "write" && x == variable && v != value) {
          false
        }
        else {
          if (action == "write" && x == variable && v == value) {
            true
          }
          else {
            searchBadWrite(variable,value,q)
          }
        }
    }
  }
  
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
          val messages2 = n.messages.updated((sender,receiver), xs)
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
