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

  case object Increment extends Message
  case class Deliver(i: BigInt) extends Message

  case class CCounter(i: BigInt) extends State
  case class VCounter(i: BigInt) extends State
  case object DummyState extends State

  case object ActorId1 extends ActorId
  case object ActorId2 extends ActorId
  case object DummyId extends ActorId

  // this protocol does not need a parameter
  case class NoParam() extends Parameter

  case class CountingActor() extends Actor {
    def init()(implicit net: VerifiedNetwork, current: ActorId) = {
      require(
        networkInvariant(net.param, net.states, net.messages, net.getActor) &&
        appendIncrement(net.messages((ActorId1,ActorId1)))
      )

      !! (ActorId1, Increment)
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))


      // ((sender, m, net.getState(current)) match {
      //   case (ActorId1, Increment, CCounter(i)) =>

      //     val j = i+1
      //     val a1a2messages = net.messages((ActorId1,ActorId2))
      //     val a1a1messages = net.messages((ActorId1,ActorId1))
      //     val newStates = net.states.updated(ActorId1, CCounter(j))
      //     val newa1a2messages = a1a2messages :+ Deliver(j)
      //     val newa1a1messages = a1a1messages :+ Increment
      //     val newMapMessages = net.messages.updated((ActorId1,ActorId2), newa1a2messages)
      //     val newnewMapMessages = newMapMessages.updated((ActorId1,ActorId1), newa1a1messages)
      //     val VCounter(k) = net.states(ActorId2)

      //     assert(areDelivers(a1a2messages))
      //     assert(appendDeliver(a1a2messages, j))
      //     assert(areIncrements(a1a1messages))
      //     assert(appendIncrement(a1a1messages))
      //     assert(areIncrements(newa1a1messages))
      //     assert(areDelivers(newa1a2messages))
      //     assert(appendDeliver(a1a2messages, j))
      //     assert(a1a2messages.isEmpty || i >= max(a1a2messages))
      //     assert(a1a2messages.isEmpty || j >= max(a1a2messages))
      //     assert(appendMax(a1a2messages, j))
      //     assert(j >= max(newa1a2messages))
      //     assert(k < j)
      //     assert(appendLarger(a1a2messages, j, k))
      //     assert(k < min(newa1a2messages))
      //     assert(isSorted(a1a2messages))
      //     assert(appendSorted(a1a2messages, j))
      //     assert(isSorted(newa1a2messages))
      //     assert(networkInvariant(net.param, newStates, newMapMessages, net.getActor))
      //     check(networkInvariant(net.param, newStates, newnewMapMessages, net.getActor))
      //     ()

      //     val messages2 = n.messages.updated((sender, receiver), xs)

      //     (sender, receiver) match {
      //       case (ActorId1(), ActorId2()) =>

      //           ((n.getState(ActorId1), m, n.getState(ActorId2)) match {
      //             case (CCounter(i), Deliver(j), VCounter(k)) =>
      //               val mm = messages2((ActorId1,ActorId2))

      //               headIsSmallest(channel) && (mm.isEmpty || j < min(mm))
      //           })

      //       case (ActorId1(), ActorId1()) =>
      //         true

      //       case _ =>
      //           false
      //     }
      //   case _ =>
      //     true
      // }

    override def validId(id: ActorId): Boolean = id == ActorId1

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork, current: ActorId) = {
      require(networkInvariant(net.param, net.states, addMessage(net.messages, sender, current, m), net.getActor) && current == ActorId1)

      (sender, m, state) match {
        case (id, Increment, CCounter(i)) if (id == current) =>
          update (CCounter(i+1))
          !! (ActorId2, Deliver(i+1))
          !! (current, Increment)

        case _ => update(DummyState)

      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

  }


  case class CheckingActor() extends Actor {
    // def receivePre(sender: ActorId, m: Message)(implicit net: VerifiedNetwork, current: ActorId) = {
    //   networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    //   sender == ActorId1 &&
    //   current == ActorId2 &&
    //   ((net getState(ActorId1), m, net getState(ActorId2)) match {
    //     case (CCounter(i), Deliver(j), VCounter(k)) =>
    //       val a1a2messages = net.messages((ActorId1,ActorId2))
    //       i >= j && j > k &&
    //         ( a1a2messages.isEmpty || j < min(a1a2messages) )
    //     case _ => false
    //   })
    // }

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork, current: ActorId) = {
      require(networkInvariant(net.param, net.states, addMessage(net.messages, sender, current, m), net.getActor))

      (sender, m, state) match {
        case (ActorId1, Deliver(j), VCounter(k)) if (j > k) => update (VCounter(j))
        case _ => update(DummyState)
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

  }

  case class DummyActor() extends Actor

}
