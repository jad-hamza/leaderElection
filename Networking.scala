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
    val myId: ActorId

    final def !!(receiver: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      net send (myId,receiver,m)
    }

    @pure
    def receivePre(sender: ActorId, m: Message)(implicit net: VerifiedNetwork): Boolean = (??? : Boolean)

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork): Unit = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && receivePre(sender, m))
      (??? : Unit)
    }

    final def state(implicit net: VerifiedNetwork) = {
      require(net.states.contains(myId))
      net.getState(myId)
    }

    final def update(s: State)(implicit net: VerifiedNetwork) = {
      net.updateState(myId, s)
    }


  }


  def runActors(p: Parameter, schedule: List[(ActorId,ActorId,Message)]): Unit = {
    require(runActorsPrecondition(p, schedule))

    val net = makeNetwork(p)

    def loop(schedule: List[(ActorId,ActorId,Message)]): Unit = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor))

      schedule match {
        case Nil() => ()
        case Cons((sender, receiver, m), schedule2) =>

          if (validId(net, sender) && validId(net, receiver) && peekMessageEnsuresReceivePre(net, sender, receiver, m) && net.applyMessage(sender, receiver, m))
            loop(schedule2)
//           else
//             error[Unit]("schedule not valid")

      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

    loop(schedule)

  }


}
