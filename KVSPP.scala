package distribution

import leon.collection._

import Protocol._
import ProtocolProof._
import Networking._
import FifoNetwork._

object PrettyPrinting {
  
  def stateToString(s: State) = {
    s match {
      case CommonState(x,h) => "CommonState"
      case BadState() => "BadState"
      case UserState() => "UserState"
    }
  }
  
  def actorIdToString(id: ActorId) = {
    id match {
      case ActorIdSys(x) => if (x==1) {"A1"}
			    else {
			      if (x==2) {"A2"}
			      else {"A3"}
			    }
      case ActorIdUser(x) => "A4"
    }
  }
  
  def statesToString(m: MMap[ActorId,State]): String = {
    def loop (l:List[ActorId]): String = {
      l match {
  	case Nil() => ""
	case Cons(x,q) => 
  	  if (m.contains(x))
	    actorIdToString(x) + " -> " + stateToString(m(x)) + "\n" + loop(q)	
	  else 
            actorIdToString(x) + " -> None \n" + loop(q)
      }
    }
    loop(List(a1,a2,a3,a4))
  }

  def getActorToString(m: MMap[ActorId,Actor]): String = {
    def loop (l:List[ActorId]): String = {
      l match {
  	case Nil() => ""
	case Cons(x,q) => 
  	  if (m.contains(x))
	    actorIdToString(x) + " -> " + actorToString(m(x)) + "\n" +loop(q)	
	  else 
            actorIdToString(x) + " -> None \n" + loop(q)
      }
    }
    loop(List(a1,a2,a3,a4))
  }
  
  def historyToString(h: List[(String,BigInt)]): String = {
    h match {
      case Nil() => ""
      case (s,i)::q => "(" + s + ", " + i + "), " + historyToString(q)
    }
  }
  
  def messageToString(m: Message) = {
    m match  {
      case Value(x) => "Value(" + x + ")"
      case Read(s) => "Read(" + s + ")"
      case WriteUser(s, i) => "WriteUser(" + s + ", " + i + ")"
      case WriteSystem(s, i, h) => "WriteSystem(" + s + ", " + i + ", " + historyToString(h) + ")"
      case WriteWaiting(s,i,h) => "WriteWaiting(" + s + ", " + i + ", " + historyToString(h) + ")"
    }
  }
  
  def messageListToString(ms: List[Message]): String = {
    ms match {
      case Nil() => "[]"
      case Cons(x, xs) =>  messageToString(x) + ", " + messageListToString(xs)
    }
  }
  
  
  def messagesToString(m: MMap[(ActorId,ActorId), List[Message]]): String = {
    actorIdToString(a1) + "," + actorIdToString(a1) + ": " + messageListToString(m.getOrElse((a1,a1), Nil())) + "\n" +
    actorIdToString(a1) + "," + actorIdToString(a2) + ": " + messageListToString(m.getOrElse((a1,a2), Nil())) + "\n" +
    actorIdToString(a1) + "," + actorIdToString(a3) + ": " + messageListToString(m.getOrElse((a1,a3), Nil())) + "\n" +
    actorIdToString(a1) + "," + actorIdToString(a4) + ": " + messageListToString(m.getOrElse((a1,a4), Nil())) + "\n" +
    actorIdToString(a2) + "," + actorIdToString(a1) + ": " + messageListToString(m.getOrElse((a2,a1), Nil())) + "\n" +
    actorIdToString(a2) + "," + actorIdToString(a2) + ": " + messageListToString(m.getOrElse((a2,a2), Nil())) + "\n" +
    actorIdToString(a2) + "," + actorIdToString(a3) + ": " + messageListToString(m.getOrElse((a2,a3), Nil())) + "\n" +
    actorIdToString(a2) + "," + actorIdToString(a4) + ": " + messageListToString(m.getOrElse((a2,a4), Nil())) + "\n" +
    actorIdToString(a3) + "," + actorIdToString(a1) + ": " + messageListToString(m.getOrElse((a3,a1), Nil())) + "\n" +
    actorIdToString(a3) + "," + actorIdToString(a2) + ": " + messageListToString(m.getOrElse((a3,a2), Nil())) + "\n" +
    actorIdToString(a3) + "," + actorIdToString(a3) + ": " + messageListToString(m.getOrElse((a3,a3), Nil())) + "\n" +
    actorIdToString(a3) + "," + actorIdToString(a4) + ": " + messageListToString(m.getOrElse((a3,a4), Nil())) + "\n" +
    actorIdToString(a4) + "," + actorIdToString(a1) + ": " + messageListToString(m.getOrElse((a4,a1), Nil())) + "\n" +
    actorIdToString(a4) + "," + actorIdToString(a2) + ": " + messageListToString(m.getOrElse((a4,a2), Nil())) + "\n" +
    actorIdToString(a4) + "," + actorIdToString(a3) + ": " + messageListToString(m.getOrElse((a4,a3), Nil())) + "\n" +
    actorIdToString(a4) + "," + actorIdToString(a4) + ": " + messageListToString(m.getOrElse((a4,a4), Nil())) + "\n" 
  }
  
  def actorToString(a: Actor) = {
    a match {
      case SystemActor(id) => "SystemActor(" + actorIdToString(id) + ")"
      case UserActor(id) => "UserActor(" + actorIdToString(id) + ")"
    }
  }
  
  def networkToString(n: VerifiedNetwork): String = {
    val VerifiedNetwork(_, states, messages, getActor) = n
    
    "\n\n" + statesToString(states) + "\n\n" + 
    messagesToString(messages) + "\n\n" + 
    getActorToString(getActor) + "\n\n"
  }
  
}
