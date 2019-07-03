package distribution


import FifoNetwork._
import Networking._

import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps


// This object contains lemmas and auxiliary functions used in the proofs

object ProtocolProof {
  import Protocol._

  def validId(net: VerifiedNetwork, id: ActorId) = {
    true
  }

  def makeNetwork(p: Parameter) = {
    val net = VerifiedNetwork(
      NoParam(),
      CMap(List[(ActorId,State)](
        (ActorId1, CCounter(0)),
        (ActorId2, VCounter(0))
      ), DummyState),
      CMap(List[Message]()),
      CMap(List[(ActorId,Actor)](
        (ActorId1, CountingActor()),
        (ActorId2, CheckingActor())
      ), DummyActor())
    )

    CountingActor().init()(net, ActorId1)

    net
  } ensuring(res => networkInvariant(res.param, res.states, res.messages, res.getActor))

  def runActorsPrecondition(p: Parameter, schedule: List[(ActorId,ActorId,Message)]): Boolean = true

  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: CMap[ActorId, State], messages: CMap[(ActorId,ActorId),List[Message]], getActor: CMap[ActorId,Actor]) = {
    states(ActorId1).isInstanceOf[CCounter] &&
    states(ActorId2).isInstanceOf[VCounter] &&
    getActor(ActorId1) == CountingActor() &&
    getActor(ActorId2) == CheckingActor() &&
    areIncrements(messages((ActorId1,ActorId1))) &&
    ((states(ActorId1),states(ActorId2)) match {
      case (CCounter(i),VCounter(k)) =>
        val channel = messages((ActorId1,ActorId2))

        areDelivers(channel) &&
        isSorted(channel) &&
        i >= k && (
          channel.isEmpty || (
            i >= max(channel) &&
            k < min(channel)
          )
        )
      case _ => false
    })
  }

  def min(l: List[Message]): BigInt = {
    require(!l.isEmpty && areDelivers(l))

    l match {
      case Cons(Deliver(i), Nil()) => i
      case Cons(Deliver(i), xs) =>
        val m = min(xs)
        if (i < m) i else m
    }
  }

  def max(l: List[Message]): BigInt = {
    require(!l.isEmpty && areDelivers(l))

    l match {
      case Cons(Deliver(i), Nil()) => i
      case Cons(Deliver(i), xs) =>
        val m = max(xs)
        if (i > m) i else m
    }
  }


  def isSorted(l: List[Message]): Boolean = {
    require(areDelivers(l))

    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(Deliver(x), ls@Cons(Deliver(y), ys)) => x < y && isSorted(ls)
    }
  }

  def areDelivers(l: List[Message]): Boolean = {
    l match {
      case Nil() => true
      case Cons(Deliver(_), xs) => areDelivers(xs)
      case _ => false
    }
  }

  @induct
  def appendDeliver(messages: List[Message], x: BigInt) = {
    require(areDelivers(messages))

    areDelivers(messages :+ Deliver(x))
  } holds

  def areIncrements(l: List[Message]): Boolean = {
    l match {
      case Nil() => true
      case Cons(Increment, xs) => areIncrements(xs)
      case _ => false
    }
  }

  @induct
  def appendIncrement(messages: List[Message]) = {
    require(areIncrements(messages))

    areIncrements(messages :+ Increment)
  } holds


  @induct
  def appendMax(l: List[Message], j: BigInt) = {
    require(areDelivers(l) && (l.isEmpty || j >= max(l)))

    appendDeliver(l,j) &&
    j >= max(l :+ Deliver(j))
  } holds

  @induct
  def appendLarger(l: List[Message], j: BigInt, k: BigInt) = {
    require(areDelivers(l) && (l.isEmpty || k < min(l)) && k < j)

    appendDeliver(l,j) &&
    k < min(l :+ Deliver(j))
  } holds

  @induct
  def appendSorted(l: List[Message], j: BigInt) = {
    require(l.isEmpty || (areDelivers(l) && isSorted(l) && j > max(l)))

    appendDeliver(l,j) &&
    isSorted(l :+ Deliver(j))
  } holds


  @induct
  def headIsSmallest(l: List[Message]) = {
    require(areDelivers(l) && !l.isEmpty && isSorted(l))

    l match {
      case Cons(Deliver(j), xs) => xs.isEmpty || j < min(xs)
    }
  } holds
}
