package distribution

import stainless.collection._
import stainless.annotation._
import stainless.proof.check
import stainless.lang._

import Protocol._
import ProtocolProof._
import Networking._

object FifoNetwork  {

  case class VerifiedNetwork(
      param: Parameter,
      var states: CMap[ActorId,State],
      var messages: CMap[(ActorId,ActorId),List[Message]],
      getActor: CMap[ActorId,Actor])  {

    def send(sender: ActorId, receiver: ActorId, m: Message): Unit = {
      messages = messages.updated((sender,receiver), messages((sender,receiver)) :+ m)
    }

    def updateState(actor: ActorId, state: State): Unit = {
      states = states.updated(actor,state)
    }

    def getState(actor: ActorId) = states(actor)

    def applyMessage(sender: ActorId, receiver: ActorId, m: Message): Boolean = {
      require(
        networkInvariant(param, states, messages, getActor) &&
        validId(this, sender) &&
        validId(this, receiver)
      )

      val channel = messages((sender,receiver))

      channel match {
        case Cons(x, xs) if (x == m) =>
          val messages2 = messages.updated((sender,receiver), xs)
          messages = messages2
          getActor(receiver).receive(sender,m)(this, receiver)
          check(networkInvariant(param, states, messages, getActor))
          true

        case _ =>
          false
      }

    } ensuring(networkInvariant(param, states, messages, getActor))
  }

}
