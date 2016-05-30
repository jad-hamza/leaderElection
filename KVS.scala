package distribution


import FifoNetwork._
import Networking._
import ProtocolProof._

import scala.language.postfixOps
import leon.lang._
import leon.proof.check
import leon.collection._
import leon.annotation._

object Protocol {
  

  case class WriteUser(s: String, i: BigInt) extends Message
  case class WriteSystem(s: String, i: BigInt, history: List[(String,BigInt)]) extends Message
  case class WriteWaiting(s: String, i: BigInt, history: List[(String,BigInt)]) extends Message
  case class Read(s: String) extends Message
  case class Value(v: BigInt) extends Message

  case class CommonState(mem: MMap[String,BigInt], history: List[(String,BigInt)]) extends State
  case class UserState() extends State
  case class BadState() extends State

  case class ActorIdSys(i: BigInt) extends ActorId
  case class ActorIdUser(i: BigInt) extends ActorId

  // this protocol does not need a parameter
  case class NoParam() extends Parameter

  val a1: ActorIdSys = ActorIdSys(1)
  val a2: ActorIdSys = ActorIdSys(2)
  val a3: ActorIdSys = ActorIdSys(3)
  val a4: ActorIdUser = ActorIdUser(1)
  
 // val a1 = ActorIdSys(1)
 // val a2 = ActorIdSys(2)
 // val a3 = ActorIdSys(3)
 // val a4 = ActorIdUser(1)

  case class SystemActor(myId: ActorId) extends Actor {
    require(myId == ActorIdSys(1) || myId == ActorIdSys(2) || myId == ActorIdSys(3))

    //var memory: MMap[String, BigInt] = MMap((x: String) => (None[BigInt]))

    def init()(implicit net: VerifiedNetwork) = {
      require(true)
    } ensuring(true)

    def checkHistory(receiverHistory: List[(String,BigInt)], messageHistory: List[(String,BigInt)]):Boolean = {
      (receiverHistory, messageHistory) match {
        case (l, Nil()) => true
        case (Nil(), l) => false
        case (x::q, y::s) => 
          if (x==y) {
            checkHistory(q,s)
          }
          else {
            checkHistory(q,y::s)
          }
      }
    }

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))

      printing("recevie System")
      (sender, m, state) match {
        case (id, WriteUser(s,i), CommonState(mem,h)) =>
	        update(CommonState(mem.updated(s,i),(s,i)::h))
	        if(myId != a1){
            !! (a1, WriteSystem(s,i,h))
          };
          if(myId != a2){
            !! (a2, WriteSystem(s,i,h))
          };
          if(myId != a3){
            !! (a3, WriteSystem(s,i,h))
          }

        case (id, WriteSystem(s,i,hs), CommonState(mem,h)) =>
	        if (checkHistory(h,hs)) {
	          update(CommonState(mem.updated(s,i),(s,i)::h));
	        }
	        else {
	          !! (myId, WriteWaiting(s,i,hs))
	        }
	      
	      case (id, WriteWaiting(s,i,hs), CommonState(mem,h)) =>
	        if (id != myId) {
	          update(BadState())
	        }
	        else { // I try to use the message as if it came from an other SystemUser
	          if (checkHistory(h,hs)) {
	            update(CommonState(mem.updated(s,i),(s,i)::h));
	          }
	          else { // I have not received enough messages, I send the message back to the Waiting List
	            !! (myId, WriteWaiting(s,i,hs))
	          }
	        }

        case (id,Read(s), CommonState(mem,h)) =>
	   	    !! (id, Value(mem.getOrElse(s,0))) //cannot return None in default case
	   	    
        case _ => update(BadState())
      }
    } ensuring(true)

  }



  case class UserActor(myId: ActorId) extends Actor {
    require(myId == ActorIdUser(1))

    var x: Option[BigInt] = None[BigInt]

    def init()(implicit net: VerifiedNetwork) = {
      net.messages = net.messages.updated((a4,a1), List(WriteUser("1", 1)))
      net.messages = net.messages.updated((a4,a2), List(Read("1"), WriteUser("1", 2), Read("1")))
      net.messages = net.messages.updated((a4,a3), List(Read("1"), Read("1")))
    }

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && (sender == a1 || sender == a2 || sender == a3))
      printing("receive User")
      (sender, m, state) match {
        case (sender, Value(v), UserState()) =>
          printing(PrettyPrinting.messageToString(Value(v)))
        case _ => update(BadState())
      }
    }  ensuring(true)


  }

  @extern
  def printing(s: String) = {
    println(s)
  }

  @ignore
  def main(args: Array[String]) = {
    println("ok")
    val actor1 = SystemActor(a1)
    val actor2 = SystemActor(a2)
    val actor3 = SystemActor(a3)
    val actor4 = UserActor(a4)

    runActors(NoParam(), actor4, List(
      (a4, a1, WriteUser("1", 1)),
      (a1, a2, WriteSystem("1", 1,Nil())),
      (a4, a2, Read("1")),
      (a2, a4,Value(1)),

      (a4, a2, WriteUser("1", 2)),
      (a4, a2, Read("1")),
      (a2, a4, Value(2)),
      (a2, a3, WriteSystem("1", 2,Nil())),
      (a4, a3, Read("1")),
      (a3, a4,Value(2)),

      (a1, a3, WriteSystem("1", 1,Nil())),
      (a4, a3, Read("1")),
      (a3, a4,Value(1))
    ))
  }


}


