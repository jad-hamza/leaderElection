package distribution

import stainless.collection._
import stainless.lang._

import Networking._
import FifoNetwork._
import Protocol._

object ProtocolProof {


  def networkInvariant(
    param: Parameter,
    states: Map[ActorId,State],
    messages: Map[(ActorId,ActorId),List[Message]],
    getActor: Map[ActorId,Actor]
  ) = {
    true
  }

  def validId(net: VerifiedNetwork, id: ActorId) = {
    true
  }

  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    true
  } holds

  def runActorsPrecondition(p: Parameter, initialActor: Actor, schedule: List[(ActorId,ActorId,Message)]) = {
    true
  }

  def initStatesFun(id: ActorId): State = Waiting()
  def initMessagesFun(ids: (ActorId,ActorId)): List[Message] = Nil()
  def initGetActorFun(id: ActorId): Actor = {
    id match {
      case ScrutId() => Scrutineer(id)
      case MemberId(_) => AssemblyMember(id)
    }
  }

  def initStates = Map(initStatesFun)
  def initMessages = Map(initMessagesFun)
  def initGetActor = Map(initGetActorFun)

  def makeNetwork(p: Parameter) = {

    VerifiedNetwork(p, initStates, initMessages, initGetActor)
  }
}