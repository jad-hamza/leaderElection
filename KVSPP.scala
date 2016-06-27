package distribution

import leon.collection._

import Protocol._
import ProtocolProof._
import Networking._
import FifoNetwork._

import scala.language.postfixOps
import leon.lang._
import leon.proof.check
import leon.collection._
import leon.annotation._

object PrettyPrinting {
  
  def stateToString(s: State) = {
    s match {
      case CommonState(x,h) => "CommonState(" + historyToString(h) + ")"
      case BadState() => "BadState"
      case UserState(l,counter) => "UserState"
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
  
  def historyToString(h: Set[(Boolean, Variable, BigInt)]): String = {
    Set.mkString(h, ",", (x:(Boolean, Variable, BigInt)) => 
    if (x._1) {
      "write(" + variableToString(x._2) + ", " + x._3 + ")"
    }
    else {
      "read(" + variableToString(x._2) + ")"
    }
    )
  }
  
  def idMessageToSring(x:(Boolean, Variable, BigInt)):String = {
    if (x._1) {
      "write(" + variableToString(x._2) + ", " + x._3 + ")"
    }
    else {
      "read(" + variableToString(x._2) + ")"
    }
  }
  
  def variableToString(x:Variable) = {
    "var(" + x.get() + ")"
  }
  
  def messageToString(m: Message) = {
    m match  {
      case Value(x, idM, h) => "Value(" + x + ", " + variableToString(idM._2) + ")"
      case Read(s) => "Read(" + variableToString(s) + ")"
      case WriteUser(s, i) => "WriteUser(" + variableToString(s) + ", " + i + ")"
      case WriteSystem(s, i,idM, h) => "WriteSystem(" + variableToString(s) + ", " + i + ", " + "id(" + idMessageToSring(idM) + "), " + historyToString(h) + ")"
      case WriteWaiting(s,i,idM, h) => "WriteWaiting(" + variableToString(s) + ", " + i + ", " + "id(" + idMessageToSring(idM) + "), " + historyToString(h) + ")"
      case AckUser(idM, h) => "AckUser(" + idMessageToSring(idM) + ", "+ historyToString(h) + ")"
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
      case SystemActor(id, l) => "SystemActor(" + actorIdToString(id) + ")"
      case UserActor(id, l) => "UserActor(" + actorIdToString(id) + ")"
    }
  }
  
  def networkToString(n: VerifiedNetwork): String = {
    val VerifiedNetwork(_, states, messages, getActor) = n
    
    "\n\n" + statesToString(states) + "\n\n" + 
    messagesToString(messages) + "\n\n" + 
    getActorToString(getActor) + "\n\n"
  }
  
}
