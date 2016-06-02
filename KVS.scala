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
  
  case class Variable(x:BigInt) {
    def get() = x
  }
  case class WriteUser(s: Variable, i: BigInt, id:(ActorId,BigInt)) extends Message
  case class AckUser(id:(ActorId,BigInt), history: Set[(ActorId, BigInt)]) extends Message
  case class WriteSystem(s: Variable, i: BigInt,id:(ActorId,BigInt), history: Set[(ActorId,BigInt)]) extends Message
  //case class WriteWaiting(s: Variable, i: BigInt,id:(ActorId,BigInt), history: Set[(ActorId,BigInt)]) extends Message
  case class Read(s: Variable) extends Message
  case class Value(v: BigInt) extends Message

  case class CommonState(mem: MMap[Variable,BigInt], history: Set[(ActorId,BigInt)]) extends State
  case class UserState(history: List[((ActorId,BigInt),Set[(ActorId,BigInt)])], counter:BigInt) extends State
  case class BadState() extends State

  case class ActorIdSys(i: BigInt) extends ActorId
  case class ActorIdUser(i: BigInt) extends ActorId

  // this protocol does not need a parameter
  case class NoParam() extends Parameter

  val a1: ActorIdSys = ActorIdSys(1)
  val a2: ActorIdSys = ActorIdSys(2)
  val a3: ActorIdSys = ActorIdSys(3)
  val a4: ActorIdUser = ActorIdUser(1)

  val channels = List[(ActorId,ActorId)](
    (a1,a1),(a1,a2),(a1,a3),(a1,a4),
    (a2,a1),(a2,a2),(a2,a3),(a2,a4),
    (a3,a1),(a3,a2),(a3,a3),(a3,a4),
    (a4,a1),(a4,a2),(a4,a3),(a4,a4)
  )
  
  val actor1 = SystemActor(a1)
  val actor2 = SystemActor(a2)
  val actor3 = SystemActor(a3)
  val actor4 = UserActor(a4)
    
    def checkHistory(receiverHistory: Set[(ActorId,BigInt)], idM:(ActorId,BigInt))(implicit net: VerifiedNetwork):Boolean = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))
     !receiverHistory.contains(idM)
    }ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  case class SystemActor(myId: ActorId) extends Actor {
    require(myId == ActorIdSys(1) || myId == ActorIdSys(2) || myId == ActorIdSys(3))

    def init()(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))
    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))

//      printing("receive System")
      (sender, m, state) match {
        case (id, WriteUser(s,i,idM), CommonState(mem,h)) =>
	        update(CommonState(mem.updated(s,i),h++Set(idM)));
	        if(myId != a1){
            !! (a1, WriteSystem(s,i,idM,h))
          };
          if(myId != a2){
            !! (a2, WriteSystem(s,i,idM,h))
          };
          if(myId != a3){
            !! (a3, WriteSystem(s,i,idM,h))
          };
          !! (a4, AckUser(idM,h))

        case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) =>
	        if (checkHistory(h,idM)) {
	          update(CommonState(mem.updated(s,i),h++Set(idM)));
	        }

        case (id,Read(s), CommonState(mem,h)) =>
          if (id == a4 && mem.contains(s)) {
              !! (id, Value(mem(s))) //cannot return None in default case
          }
  	    
        case _ => ()
//          update(BadState())
      }
    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))

  }



  case class UserActor(myId: ActorId) extends Actor {
    require(myId == ActorIdUser(1))

    var x: Option[BigInt] = None[BigInt]


    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(myId, net))
      state match {
        case UserState(l,counter) =>
          //!! (a1,WriteUser(Variable(1), 1, (a4,counter)))
          update(UserState( Cons (((a4,1),Set()), l), counter+1))
        case BadState() => ()
      }

    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))


    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require (receivePre(this,sender,m))
//      printing("receive User");
      (sender, m, state) match {
        case (sender, Value(v), UserState(x,counter)) =>
          ()
//          printing(PrettyPrinting.messageToString(Value(v)))
        case _ => ()
//          update(BadState())
      }
    }  ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))


  }

//  @extern
//  def printing(s: String) = {
//    println(s)
//  }

  @ignore
  def main(args: Array[String]) = {
    println("ok")
    val actor1 = SystemActor(a1)
    val actor2 = SystemActor(a2)
    val actor3 = SystemActor(a3)
    val actor4 = UserActor(a4)

    //runActors(NoParam(), actor4, List(
    //  (a4, a1, WriteUser("1", 1)),
    //  (a1, a2, WriteSystem("1", 1,Set())),
    //  (a4, a2, Read("1")),
    //  (a2, a4,Value(1)),

    //  (a4, a2, WriteUser("1", 2)),
    //  (a4, a2, Read("1")),
    //  (a2, a4, Value(2)),
    //  (a2, a3, WriteSystem("1", 2,Set())),
    //  (a4, a3, Read("1")),
    //  (a3, a4,Value(2)),

    //  (a1, a3, WriteSystem("1", 1,Set())),
    //  (a4, a3, Read("1")),
    //  (a3, a4,Value(1))
  // ))
  }


}


