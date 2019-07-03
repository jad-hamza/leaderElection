package distribution


import FifoNetwork._
import Networking._
import ProtocolProof._
import Quantifiers._

import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._

import scala.language.postfixOps

// following https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm

object Protocol {

  case class Election(i: BigInt) extends Message
  case class Elected(i: BigInt) extends Message

  case class NonParticipant() extends State
  case class Participant() extends State
  case class KnowLeader(i: BigInt) extends State

  case class UID(uid: BigInt) extends ActorId
  case object DummyId extends ActorId


  case class DummyActor(myId: ActorId) extends Actor

  case class Process(myId: ActorId, ssn: BigInt) extends Actor {
    require(myId.isInstanceOf[UID])

    val UID(myuid) = myId

    def init()(implicit net: VerifiedNetwork) = {
      require(networkInvariant(net.param, net.states, net.messages, net.getActor) && validParam(net.param) && myuid == starterProcess )

      val Params(n, starterProcess, ssns) = net.param
      val states = net.states
      val messages = net.messages
      val getActor = net.getActor

      assert(0 <= myuid && myuid < n)
      assert(elimForAll(n, getActorDefinition(getActor), myuid))
      assert(getActor(UID(myuid)) == this)
      assert(intForAll(n, emptyChannel(n, messages)))
      val newMessages = messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn)))
      assert(stillRingChannels(n, n, n, messages, myuid, increment(myuid, n), List(Election(ssn))))
      assert(elimForAll(n, emptyChannel(n, messages), myuid))
      assert(emptyToSmallChannel(n, n, messages, myuid, increment(myuid, n), List(Election(ssn))))
      assert(emptyToOneChannel(n, n, n, messages, myuid, increment(myuid, n), List(Election(ssn))))
      assert(intForAll(n, noLeader(n, states)))
      assert(stillNoLeader(n, states, myuid, Participant()))
      assert(intForAll(n, noLeader(n, states.updated(UID(myuid), Participant()))))
      assert(intForAll(n, noLeader(n, states.updated(UID(myuid), Participant()))))
      assert(noLeaderImpliesNoLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages))
      assert(intForAll(n, noLeaderDuringElection(n, states.updated(UID(myuid), Participant()), newMessages)))
      assert(ssn == collectMaxSSN(n, starterProcess, starterProcess, getActor))
      assert(ssn == collectMaxSSN(n, starterProcess, myuid, getActor))
      assert(stillElectingMax(n, n, starterProcess, messages, getActor, myuid, ssn))
      assert(intForAll(n, electingMax(n, starterProcess, messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))), getActor)))
      assert(newMessages == messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))))
      assert(intForAll(n, electingMax(n, starterProcess, newMessages, getActor)))
      assert(nothingExists(n, messages, isElectedMessage))
      assert(updateChannel(n, messages, List(Election(ssn)), isElectedMessage, myuid, increment(myuid, n)))
      assert(!existsMessage(n, messages.updated((UID(myuid), UID(increment(myuid,n))),List(Election(ssn))), isElectedMessage))
      assert(!existsMessage(n, newMessages, isElectedMessage))
      assert(states.updated(UID(myuid), Participant())(UID(starterProcess)) == Participant())
      assert(forAllModulo(n, starterProcess, starterProcess, isParticipant(n, states.updated(UID(myuid), Participant()))))
      assert(stillElectionParticipants(n, n, starterProcess, myuid, states.updated(UID(myuid), Participant()), messages, List(Election(ssn))))
      assert(intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), messages.updated((UID(myuid), UID(increment(myuid, n))), List(Election(ssn))))))
      assert(intForAll(n, electionParticipants(n, starterProcess, states.updated(UID(myuid), Participant()), newMessages)))
      assert(noElectedImpliesElectedMax(n, n, starterProcess, newMessages, getActor))
      assert(intForAll(n, electedMax(n, starterProcess, newMessages, getActor)))
      assert(noLeaderImpliesKnowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor))
      assert(intForAll(n, knowTrueLeader(n, starterProcess, states.updated(UID(myuid), Participant()), getActor)))
      assert(networkInvariant(net.param, states.updated(UID(myuid), Participant()), newMessages, getActor))

      val nextProcess = UID(increment(myuid, n))
      update(Participant())
      !! (nextProcess, Election(ssn))
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))


    def receivePre(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {

      val Params(n, starterProcess, ssns) = net.param
      val states = net.states
      val messages = net.messages
      val getActor = net.getActor
      val UID(usender) = sender

      intForAll(n, emptyChannel(n, messages)) &&
      networkInvariant(net.param, states, messages, getActor) &&
      0 <= usender && usender < n &&
      0 <= myuid && myuid < n && myuid == increment(usender,n)
    }

/**
      &&
      intForAll(n, getActorDefinition(getActor)) &&
      elimForAll(n, getActorDefinition(getActor), myuid) &&
      getActor(UID(myuid)) == this &&
      (m match {
        case Election(ssn2) =>
          intForAll(n, noLeader(n, states)) && (
            ssn2 == collectMaxSSN(n, starterProcess, usender, net.getActor) ||
            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), net.getActor)
            ) &&
          forAllModulo(n, starterProcess, usender, isParticipant(n, states))
        case Elected(ssn2) =>
          ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)
      }) &&
      elimForAll(n, emptyChannel(n, messages), myuid) &&
      ((sender, m, this.state) match {
        case (id, Election(ssn2), NonParticipant()) =>
          if (ssn2 != ssn) {
            //               update (Participant())
            //               !! (UID(increment(myuid,n)), Election(uid))
            receivePreBranch1(n, starterProcess, usender, this, states, messages, getActor, ssns, ssn2)
          }
          else {
            true
            //              receivePreBranch2(n, starterProcess, usender, myuid, states, messages, getActor, ssns, ssn2) &&
            //              false
            // I cannot receive an Election message equal to my uid if I'm not a participant
            //              forAllModulo(n, starterProcess, usender, isParticipant(n, states))
            //               false
          }

        case (id, Election(ssn2), Participant()) =>
          if (ssn2 > ssn) {
            //               !! (nextProcess, Election(uid))

            //          intForAll(n, emptyChannel(n, messages)) &&
            //          m == Election(ssn2) &&
            //          intForAll(n, noLeader(n, states)) &&
            //          forAllModulo(n, starterProcess, usender, isParticipant(n, net.states)) &&
            //          (
            //            ssn2 == collectMaxSSN(n, starterProcess, usender, getActor) ||
            //            ssn2 == collectMaxSSN(n, starterProcess, decrement(starterProcess, n), getActor)) &&
            //          ssn2 > ssn &&
            receivePreBranch3(n, starterProcess, usender, this, states, messages, getActor, ssns, ssn2)

          } else if (ssn2 == ssn) {
            //               update (KnowLeader(uid))
            //               !! (nextProcess, Elected(myuid))

            receivePreBranch4(n, starterProcess, usender, this, states, messages, getActor, ssns, ssn2)

          } else {
            true
            // discard smaller uid Election message
          }

        case (id, Elected(_), NonParticipant()) =>
          // I cannot receive an Elected message if I didn't even participate yet
          true
        //             false

        case (id, Elected(ssn2), Participant()) => {
          //               update (KnowLeader(uid))
          //               !! (nextProcess, Elected(uid))
          receivePreBranch5(n, starterProcess, usender, this, states, messages, getActor, ssns, ssn2)
        }

        case (id, Elected(uid), KnowLeader(uid2)) => {
          //             uid == uid2
          true
        }

        case (id, Election(_), KnowLeader(_)) =>
          // there cannot be an election going on if I already know the Leader
          true
        //             false

        case _ => {
          true
          //             false
        }
      })
    }
*/

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(sender, m))

      val Params(n, starterProcess, ssns) = net.param
      val nextProcess = UID(increment(myuid, n))

      (sender, m, state) match {
        case (id, Election(ssn2), NonParticipant()) =>
          if (ssn != ssn2) {
            val packet = if (ssn > ssn2) Election(ssn) else Election(ssn2)

            update (Participant())
            !! (nextProcess, packet)
          }
          else {
            // I cannot receive an Election message equal to my ssn if I'm not a participant
//             assert(false)
            ()
          }

        case (id, Election(ssn2), Participant()) =>
          if (ssn2 > ssn) {
            !! (nextProcess, Election(ssn2))
          } else if (ssn == ssn2) {
            update (KnowLeader(ssn))
            !! (nextProcess, Elected(ssn))
            // I'm the leader!!
          } else {
            // discard smaller ssn Election message
          }

        case (id, Elected(ssn2), Participant()) => {
          update (KnowLeader(ssn2))
          !! (nextProcess, Elected(ssn2))
        }

        case (id, Elected(_), NonParticipant()) =>
          // I cannot receive an Elected message if I didn't even participate yet
//           assert(false)
            ()

        case _ => {
//           assert(false)
          ()
        }

      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))

  }

}

