package distribution

import leon.collection._
import leon.lang._

import Networking._
import FifoNetwork._
import Protocol._

object ProtocolProof {


  def networkInvariant(
    param: Parameter,
    states: MMap[ActorId,State],
    messages: MMap[(ActorId,ActorId),List[Message]],
    getActor: MMap[ActorId,Actor]
  ) = {
    true
  }

  def validId(net: VerifiedNetwork, id: ActorId) = {
    true
  }

  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    true
  } holds

  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]) = {
    true
  }

  def init_states_fun(id: ActorId): State = Waiting()
  def init_messages_fun(ids: (ActorId,ActorId)): List[Message] = Nil()
  def init_getActor_fun(id: ActorId): Actor = {
    id match {
      case ScrutId() => Scrutineer(id)
      case MemberId(_) => AssemblyMember(id)
    }
  }

  def init_states = MMap(init_states_fun)
  def init_messages = MMap(init_messages_fun)
  def init_getActor = MMap(init_getActor_fun)

  def makeNetwork(p: Parameter) = {

    VerifiedNetwork(p, init_states, init_messages, init_getActor)
  }
}