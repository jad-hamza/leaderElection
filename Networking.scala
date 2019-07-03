package distribution

import Protocol._
import ProtocolProof._
import FifoNetwork._

import stainless.collection._
import stainless.proof.check
import stainless.lang._
import stainless.annotation._

object Networking {

  abstract class ActorId
  abstract class Message
  abstract class State
  abstract class Parameter


  abstract class Actor {
    final def !!(receiver: ActorId, m: Message)(implicit net: VerifiedNetwork, current: ActorId) = {
      net send (current, receiver, m)
    }

    def validId(id: ActorId): Boolean = true

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork, current: ActorId): Unit = {
      require(networkInvariant(net.param, net.states, addMessage(net.messages, sender, current, m), net.getActor) && validId(current))
      (??? : Unit)
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

    final def state(implicit net: VerifiedNetwork, current: ActorId) = net.getState(current)

    final def update(s: State)(implicit net: VerifiedNetwork, current: ActorId) = {
      net.updateState(current, s)
    }


  }

  def addMessage(messages: CMap[(ActorId, ActorId), List[Message]], sender: ActorId, current: ActorId, m: Message) = {
    messages.updated((sender, current), Cons(m, messages((sender,current))))
  }


  def runActors(p: Parameter, schedule: List[(ActorId,ActorId,Message)]): Unit = {
    require(runActorsPrecondition(p, schedule))

    val net = makeNetwork(p)

    def loop(schedule: List[(ActorId,ActorId,Message)]): Unit = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))

      schedule match {
        case Nil() => ()
        case Cons((sender, receiver, m), schedule2) =>

          if (validId(net, sender) && validId(net, receiver) && net.applyMessage(sender, receiver, m))
            loop(schedule2)
//           else
//             error[Unit]("schedule not valid")

      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

    loop(schedule)

  }


}
