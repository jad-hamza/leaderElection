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
  case class WriteSystem(s: String, i: BigInt) extends Message
  case class Read(s: String) extends Message
  case class Value(v: BigInt) extends Message

  case class CommonState(mem: MMap[String,BigInt]) extends State
  case class BadState() extends State

  case class ActorIdSys(i: BigInt) extends ActorId
  case class ActorIdUser(i: BigInt) extends ActorId

  // this protocol does not need a parameter
  case class NoParam() extends Parameter

  val actor1: ActorIdSys = ActorIdSys(1)
  val actor2: ActorIdSys = ActorIdSys(2)
  val actor3: ActorIdSys = ActorIdSys(3)
  val actor4: ActorIdUser = ActorIdUser(1)
  
  val a1 = ActorIdSys(1)
  val a2 = ActorIdSys(2)
  val a3 = ActorIdSys(3)
  val a4 = ActorIdUser(1)

  case class SystemActor(myId: ActorId) extends Actor {
    require(myId == ActorIdSys(1) || myId == ActorIdSys(2) || myId == ActorIdSys(3))

    //var memory: MMap[String, BigInt] = MMap((x: String) => (None[BigInt]))

    def init()(implicit net: VerifiedNetwork) = {
      require(true)
    } ensuring(true)


    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))

      printing("recevie System")
      (sender, m, state) match {
        case (id, WriteUser(s,i), CommonState(x)) =>
          val memory = this.state(net);
	  memory match {
	    case CommonState(mem) => 
	      update(CommonState(mem.updated(s,i)))
	    case BadState() => update(BadState())
	  }
          if(myId != actor1){
            !! (actor1, WriteSystem(s,i))
          };
          if(myId != actor2){
            !! (actor2, WriteSystem(s,i))
          };
          if(myId != actor3){
            !! (actor3, WriteSystem(s,i))
          }

        case (id, WriteSystem(s,i), CommonState(x)) =>
          val memory = this.state(net);
	  memory match {
	    case CommonState(mem) => 
	      update(CommonState(mem.updated(s,i)));
	    case BadState() => update(BadState())
	  }

        case (id,Read(s), CommonState(x)) =>
           val memory = this.state(net);
	   memory match {
	     case CommonState(mem) => 
	   	!! (id, Value(mem.getOrElse(s,0))) //cannot return None in default case
	     case BadState() => update(BadState())
	   }
        case _ => update(BadState())
      }
    } ensuring(true)

  }



  case class UserActor(myId: ActorId) extends Actor {
    require(myId == ActorIdUser(1))

    var x: Option[BigInt] = None[BigInt]

    def init()(implicit net: VerifiedNetwork) = ()

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && (sender == actor1 || sender == actor2 || sender == actor3))
      printing("receive User")
      (sender, m, state) match {
        case (sender, Value(v), CommonState(x)) =>
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
    val a1 = SystemActor(actor1)
    val a2 = SystemActor(actor2)
    val a3 = SystemActor(actor3)
    val a4 = UserActor(actor4)

    runActors(NoParam(), a1, List(
      (actor4, actor1, WriteUser("1", 1)),
      (actor1, actor2, WriteSystem("1", 1)),
      (actor4, actor2, Read("1")),
      (actor2,actor4,Value(1)),

      (actor4, actor2, WriteUser("1", 2)),
      (actor4,actor2, Read("1")),
      (actor2, actor4, Value(2)),
      (actor2, actor3, WriteSystem("1", 2)),
      (actor4, actor3, Read("1")),
      (actor3,actor4,Value(2)),

      (actor1, actor3, WriteSystem("1", 1)),
      (actor4, actor3, Read("1")),
      (actor3,actor4,Value(1))
    ))
  }


}


