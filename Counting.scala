package distribution


import FifoNetwork._
import Networking._

import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps


object Protocol {
  import ProtocolProof._

  case class Increment() extends Message
  case class Deliver(i: BigInt) extends Message

  case class CCounter(i: BigInt) extends State
  case class VCounter(i: BigInt) extends State
  case class BadState() extends State

  case class ActorId1() extends ActorId
  case class ActorId2() extends ActorId

  // this protocol does not need a parameter
  case class NoParam() extends Parameter

  val actor1: ActorId = ActorId1()
  val actor2: ActorId = ActorId2()

  case class CountingActor(myId: ActorId) extends Actor {
    require(myId == actor1)

    def init()(implicit net: VerifiedNetwork) = {
      require(
        networkInvariant(net.param, net.states, net.messages, net.getActor) &&
        appendIncrement(net.messages.getOrElse((actor1,actor1), Nil()))
      )

      !! (actor1,Increment())
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

    def receivePre(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      countingActorReceivePre(this, sender, m)
    }

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && receivePre(sender, m))

      (sender, m, state) match {
        case (id,Increment(),CCounter(i)) if (id == myId) =>
          update (CCounter(i+1))
          !! (actor2, Deliver(i+1))
          !! (myId, Increment())

        case _ => update(BadState())

      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

  }


  case class CheckingActor(myId: ActorId) extends Actor {
    require(myId == actor2)

    def receivePre(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      checkingActorReceivePre(this, sender, m)
    }

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && receivePre(sender, m))
      check(sender == ActorId1())

      (sender, m, state) match {

        case (ActorId1(), Deliver(j), VCounter(k)) if (j > k) => update (VCounter(j))
        case _ => update(BadState())
      }
    }  ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))


  }

  @ignore
  def main(args: Array[String]) = {
    val a1 = CountingActor(actor1)
    val a2 = CheckingActor(actor2)

    runActors(NoParam(), List(
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor2, Deliver(1)),
      (actor1, actor2, Deliver(2)),
      (actor1, actor2, Deliver(3)),
      (actor1, actor2, Deliver(4)),
      (actor1, actor2, Deliver(5))
    ))
  }


}


