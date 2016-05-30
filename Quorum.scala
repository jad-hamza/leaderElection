package distribution

import Networking._
import FifoNetwork._

object Protocol {

  case class ScrutId() extends ActorId
  case class MemberId(i: BigInt) extends ActorId

  case class Waiting() extends State


  def isMemberId(id: ActorId) = {
    id match {
      case MemberId(_) => true
      case _ => false
    }
  }

  case class Scrutineer(id: ActorId) extends Actor {
    require(id == ScrutId())

    def init()(implicit net: VerifiedNetwork) = {}

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {}
  }

  case class AssemblyMember(id: ActorId) extends Actor {
    require(isMemberId(id))


    def init()(implicit net: VerifiedNetwork) = {}

    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {}

  }
}