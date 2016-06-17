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
  case class WriteUser(s: Variable, i: BigInt) extends Message
  case class AckUser(id:(Boolean, Variable, BigInt), history: Set[(Boolean, Variable, BigInt)]) extends Message
  case class WriteSystem(s: Variable, i: BigInt,id:(Boolean, Variable, BigInt), history: Set[(Boolean, Variable, BigInt)]) extends Message
  case class WriteWaiting(s: Variable, i: BigInt,id:(Boolean, Variable, BigInt), history: Set[(Boolean, Variable, BigInt)]) extends Message
  case class Read(s: Variable) extends Message
  case class Value(v: BigInt, idM: (Boolean, Variable, BigInt), history: Set[(Boolean, Variable, BigInt)]) extends Message

  case class CommonState(mem: MMap[Variable,BigInt], history: Set[(Boolean, Variable, BigInt)]) extends State
  case class UserState(history: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])], counter:BigInt) extends State
  case class BadState() extends State

  case class ActorIdSys(i: BigInt) extends ActorId
  case class ActorIdUser(i: BigInt) extends ActorId

  // this protocol does not need a parameter
  case class Variables(variables: List[Variable]) extends Parameter

  val correct_variables = List(Variable(1))
  
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
  
  val actor1 = SystemActor(a1, List(a2,a3))
  val actor2 = SystemActor(a2, List(a1,a3))
  val actor3 = SystemActor(a3, List(a1,a2))
  val actor4 = UserActor(a4)
    
  def checkHistory(receiverHistory: Set[(Boolean, Variable, BigInt)], messageHistory: Set[(Boolean, Variable, BigInt)])(implicit net: VerifiedNetwork):Boolean = {
    require(networkInvariant(net.param, net.states, net.messages, net.getActor))
    messageHistory.subsetOf(receiverHistory)
  }ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))
  
  case class SystemActor(myId: ActorId, otherActor: List[ActorId]) extends Actor {

    def init()(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))
    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))

    def broadcastAck(otherActor: List[ActorId], m: Message)(implicit net: VerifiedNetwork): Unit = {
      require(broadcastAckPre(this, otherActor, m, net.param, net.states, net.messages, net.getActor))
      otherActor match {
        case Nil() => 
          val WriteSystem(s,i,idM,h) = m
          //!! (a4, AckUser(idM, h))
        case Cons(x, xs) => 
          //!! (x, m)
          //broadcastAck(xs, m)
      }
    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
        
        val Variables(variables) = net.param
        
//      printing("receive System")
      (sender, m, state) match {
        case (id, WriteUser(s,i), CommonState(mem,h)) =>
          val idM = (true, s, i)
          update(CommonState(mem.updated(s,i),h++Set(idM)));
          broadcastAck(otherActor, WriteSystem(s,i,idM,h))
//           !! (a1, WriteSystem(s,i,idM,h))
//           !! (a2, WriteSystem(s,i,idM,h))
//           !! (a3, WriteSystem(s,i,idM,h))
//           !! (a4, AckUser(idM,h))
            
        case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) =>
	        if (id != myId && (idM == (true, s, i))) {
            if (checkHistory(h,hs)) {
              update(CommonState(mem.updated(s,i),h++Set(idM)));
            }
            else {
                !! (myId,WriteWaiting(s,i,idM,hs))
            }
          }
        
        case (id,WriteWaiting(s,i,idM,hs), CommonState(mem,h)) =>
          if (idM == (true, s, i)) {
            if (checkHistory(h,hs)) {
              update(CommonState(mem.updated(s,i),h++Set(idM)));
            }
            else {
                  !! (myId,WriteWaiting(s,i,idM,hs))
            }
          }

        case (id,Read(s), CommonState(mem,h)) =>
          if (id == a4 && {
          val Variables(variables) = net.param
          variables.contains(s)
          }) {
              !! (id, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h))
          }
  	    
        case _ => ()
//          update(BadState())
      }
    } ensuring(networkInvariant(net.param, net.states, net.messages, net.getActor))

  }

  case class UserActor(myId: ActorId) extends Actor {

    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(myId, net))
      val Variables(variables) = net.param
      state match {
        case UserState(l,counter) =>
          !! (a1,WriteUser(Variable(1), 1))
          update(UserState( Cons (((true, Variable(1), 1),Set()), l), counter))
        case _ => ()
      }

    } ensuring{networkInvariant(net.param, net.states, net.messages, net.getActor)}


    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require (receivePre(this,sender,m))
      (sender, m, state) match {
        case (sender, Value(v,idM,h), UserState(x,counter)) =>
          update(UserState(Cons((idM,h),x),counter))
//          printing(PrettyPrinting.messageToString(Value(v)))
        case (sender, AckUser(idM,h), UserState(x,counter)) => 
          update(UserState(Cons((idM,h),x),counter))
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
//     val actor1 = SystemActor(a1)
//     val actor2 = SystemActor(a2)
//     val actor3 = SystemActor(a3)
//     val actor4 = UserActor(a4)

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


