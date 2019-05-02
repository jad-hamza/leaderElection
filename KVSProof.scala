package distribution


import FifoNetwork._
import Networking._
import Protocol._

import stainless.lang._
import stainless.collection._
import stainless.proof._
import stainless.annotation._
import stainless.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof {
  import Protocol._
  import PrettyPrinting._
  import ProtocolProof2._
  import ProtocolProof3._

  def subsetOf(l1: List[ActorId], l2: List[ActorId]): Boolean = {
    l1 match {
      case Nil() => true
      case Cons(x,xs) =>
        l2.contains(x) &&
        subsetOf(xs, l2)
    }
  }

  def emptyNet(): VerifiedNetwork = {
    VerifiedNetwork(
      Param(List(), List()),
      init_states,
      init_messages,
      init_getActor
    )
  }

  def areWU(list: List[(ActorId,Message)]): Boolean = {
    list match {
      case Cons(x,xs) if (!isWU(x._2)) => false
      case Cons(_,xs) => areWU(xs)
      case Nil() => true
    }
  }

  def isWU(m: Message) = {
    m match {
      case WriteUser(s,i) => true
      case _ => false
    }
  }

  def isWS(m: Message) = {
    m match {
      case WriteSystem(s,i,id,h) => true
      case _ => false
    }
  }

  def isWW(m: Message) = {
    m match {
      case WriteWaiting(s,i,id,h) => true
      case _ => false
    }
  }

  def collectWUsInit(l: List[(ActorId,Message)]): Set[Message] = {
    l match {
      case Nil() => Set()
      case Cons((id,WriteUser(s,i)), xs) => collectWUsInit(xs) ++ Set(WriteUser(s,i))
      case Cons(_,xs) => collectWUsInit(xs)
    }
  }

  def newContains(x:Message, list: List[(ActorId, Message)]): Boolean = {
    list match {
      case Nil() => false
      case Cons(h,t) if (h._2==x) => true
      case Cons(h,t) => newContains(x,t)
    }
  }

  def differentInitMessage(list: List[(ActorId, Message)], messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    list match {
      case Nil() => true
      case Cons(x,xs) =>
        !newContains(x._2,xs) &&
        !collectWUsList(messages, channels).contains(x._2) &&
        differentInitMessage(xs, messages)
    }
  }

  def differentInitMessageWS(list: List[(ActorId, Message)], messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    list match {
      case Nil() => true
      case Cons(x,xs) =>
        !newContains(x._2,xs) &&
        !collectWSsList(messages, channels).contains(x._2) &&
        differentInitMessageWS(xs, messages)
    }
  }

  def differentInitMessageWW(list: List[(ActorId, Message)], messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    list match {
      case Nil() => true
      case Cons(x,xs) =>
        !newContains(x._2,xs) &&
        !collectWWsList(messages, channels).contains(x._2) &&
        differentInitMessageWW(xs, messages)
    }
  }

  def removeDiff(list: List[(ActorId, Message)], messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    require(
      areWU(list) &&
      differentInitMessage(list, messages) &&
      differentInitMessageWS(list, messages) &&
      differentInitMessageWW(list, messages)
    )

    list match {
      case Nil() => true
      case Cons(x,Nil())=> true
      case Cons(x,xs@Cons(y,ys)) =>
        !newContains(x._2, xs) &&
        !newContains(y._2, ys) &&
        addCollectWU(messages, (a4,x._1), x._2, channels) &&
        (x._2 != y._2) &&
        addCollect2(messages, (a4,x._1), x._2, channels) &&
        (x._2 != y._2) &&
        addCollect3(messages, (a4,x._1), x._2, channels) &&
        (x._2 != y._2) &&
        !collectWUsList(add(messages, (a4,x._1), x._2), channels).contains(y._2) &&
        !collectWSsList(add(messages, (a4,x._1), x._2), channels).contains(y._2) &&
        !collectWWsList(add(messages, (a4,x._1), x._2), channels).contains(y._2) &&
        removeDiff(Cons(x,ys), messages) &&
        differentInitMessage(xs, add(messages, (a4,x._1), x._2)) &&
        differentInitMessageWS(xs, add(messages, (a4,x._1), x._2)) &&
        differentInitMessageWW(xs, add(messages, (a4,x._1), x._2))

    }
  }holds

  def collectContains(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    m: Message
    ): Boolean = {
      require(!collectWUsList(messages, channels).contains(m)&&
      channels.contains(c) &&
      {
        m match {
          case WriteUser(s,i) => true
          case _ => false
        }
      })
      !collectWUs(messages.getOrElse(c, Nil())).contains(m) &&
      colLis(messages.getOrElse(c, Nil()), m) &&
      !messages.getOrElse(c, Nil()).contains(m) &&
      true
   } holds

  def colLis(l: List[Message], m: Message): Boolean = {
    require(
      !collectWUs(l).contains(m) && {
        m match {
          case WriteUser(s,i) => true
          case _ => false
        }
      }
    )

    l match {
      case Nil() => true
      case Cons(x,xs) if (x==m) => collectWUs(l).contains(m)
      case Cons(x,xs) => colLis(xs,m) && !l.contains(m)
    }
  }holds


  def distinctElements[A](list: List[A]): Boolean = {
    list match {
      case Nil() => true
      case Cons(x,xs) =>
        !xs.contains(x) &&
        distinctElements(xs)
    }
  }

  def distinctElementsInit(list: List[(ActorId, Message)]): Boolean = {
    list match {
      case Nil() => true
      case Cons(x,xs) =>
        !newContains(x._2,xs) &&
        distinctElementsInit(xs)
    }
  }

  def validId(net: VerifiedNetwork, id: ActorId) = {
    id == a1 || id == a2 || id == a3 || id == a4
  }

  def inChannels(net: VerifiedNetwork, id1:ActorId, id2:ActorId) = {
    require(validId(net,id1) && validId(net,id2))
    channels.contains((id1,id2))
  }holds


//   def makeInitMem(l: List[Variable]): List[(Variable,BigInt)] = {
//     require(!l.isEmpty)
//     l match {
//       case Cons(x,Nil()) => List((x,0))
//       case Cons(x,xs) => Cons((x,0),makeInitMem(xs))
//     }
//   }
//
//   val init_mem = makeInitMem(correct_variables)

  val init_mem = Map[Variable, BigInt](
    Map[Variable, BigInt]()
  )

//   val init_param = Variables(correct_variables)

  /*
  val init_messages_list = List[((ActorId,ActorId),List[Message])](
    ((a1,a1),(Nil():List[Message])),
    ((a1,a2),(Nil():List[Message])),
    ((a1,a3),(Nil():List[Message])),
    ((a1,a4),(Nil():List[Message])),
    ((a2,a1),(Nil():List[Message])),
    ((a2,a2),(Nil():List[Message])),
    ((a2,a3),(Nil():List[Message])),
    ((a2,a4),(Nil():List[Message])),
    ((a3,a1),(Nil():List[Message])),
    ((a3,a2),(Nil():List[Message])),
    ((a3,a3),(Nil():List[Message])),
    ((a3,a4),(Nil():List[Message])),
    ((a4,a1),(Nil():List[Message])),
    ((a4,a2),(Nil():List[Message])),
    ((a4,a3),(Nil():List[Message])),
    ((a4,a4),(Nil():List[Message]))
    )
  val init_messages1 = Map.makeMap[(ActorId,ActorId),List[Message]](init_messages_list)
  val init_messages = init_messages1.updated((a4,a4), Nil())
  */


//   val init_states_list = List[(ActorId, State)](
//     (a1,CommonState(Map.makeMap[Variable,BigInt](init_mem), Set())),
//     (a2,CommonState(Map.makeMap[Variable,BigInt](init_mem), Set())),
//     (a3,CommonState(Map.makeMap[Variable,BigInt](init_mem), Set())),
//     (a4,UserState(Nil(),0))
//     )
//   val init_states = Map.makeMap[ActorId,State](init_states_list)

  val init_states = Map[ActorId, State](
    Map[ActorId, State](
      (a1,CommonState(init_mem, Set())),
      (a2,CommonState(init_mem, Set())),
      (a3,CommonState(init_mem, Set())),
      (a4,UserState(Nil(),0))
    )
  )

//   val init_getActor_list = List[(ActorId,Actor)](
//     (a1,SystemActor(a1, List(a2,a3))),
//     (a2,SystemActor(a2, List(a1,a3))),
//     (a3,SystemActor(a3, List(a1,a2))),
//     (a4,UserActor(a4))
//     )
//   val init_getActor = Map.makeMap[ActorId,Actor](init_getActor_list)

  val init_getActor = Map[ActorId, Actor](
    Map[ActorId, Actor](
      (a1,SystemActor(a1, List(a2,a3))),
      (a2,SystemActor(a2, List(a1,a3))),
      (a3,SystemActor(a3, List(a1,a2))),
      (a4,UserActor(a4))
    )
  )

  val init_messages = Map[(ActorId, ActorId), List[Message]](
    Map[(ActorId, ActorId), List[Message]](
      ((a1,a1),(Nil():List[Message])),
      ((a1,a2),(Nil():List[Message])),
      ((a1,a3),(Nil():List[Message])),
      ((a1,a4),(Nil():List[Message])),
      ((a2,a1),(Nil():List[Message])),
      ((a2,a2),(Nil():List[Message])),
      ((a2,a3),(Nil():List[Message])),
      ((a2,a4),(Nil():List[Message])),
      ((a3,a1),(Nil():List[Message])),
      ((a3,a2),(Nil():List[Message])),
      ((a3,a3),(Nil():List[Message])),
      ((a3,a4),(Nil():List[Message])),
      ((a4,a1),(Nil():List[Message])),
      ((a4,a2),(Nil():List[Message])),
      ((a4,a3),(Nil():List[Message])),
      ((a4,a4),(Nil():List[Message]))
    )
  )

  def checkContent[A,B](l: List[(A,B)], m: Map[A,B]): Boolean  = {
    l match {
      case Nil() => true
      case Cons((x,v), xs) => m.contains(x) && checkContent(xs, m)
    }
  }

  def makeNetwork(p: Parameter) = {
    require(validParam(p))
    VerifiedNetwork(p,
		init_states,
		init_messages,
		init_getActor
		)
  }ensuring(res =>
    res.getActor(a1) == SystemActor(a1, List(a2,a3)) &&
    res.getActor(a2) == SystemActor(a2, List(a1,a3)) &&
    res.getActor(a3) == SystemActor(a3, List(a1,a2)) &&
    res.getActor(a4) == UserActor(a4) &&
    areInChannelsInit1() &&
    areInChannelsInit2() &&
    areInChannelsInit3() &&
    areInChannelsBisInit1() &&
    areInChannelsBisInit2() &&
    areInChannelsBisInit3() &&
    writeEmpty(res.states) &&
    WriteHistory(res.messages, res.states) &&
    initTableHistory(res.param, res.states) &&
    tableHistory(res.param, res.states) &&
    messagesEmpty(channels) &&
    not2WriteUser(channels, res.messages) &&
    res.messages == init_messages &&
    initMessageEmpty() &&
    uniqueWriteUser(res.messages, channels) &&
    prop3(res.messages, channels) &&
    initProp5(init_messages, channels) &&
    prop5(res.messages, channels) &&
    initProp7(init_messages, channels) &&
    initProp4(init_messages, channels, init_states, List(a1,a2,a3)) &&
    initProp9(init_messages, channels) &&
    initProp10(init_messages, channels) &&
    initProp8(init_messages, channels, init_states) &&
    networkInvariant(res.param,res.states, res.messages, res.getActor) &&
    true
  )


  def validParam(p: Parameter): Boolean = {
    val Param(variables, initMessages) = p
    areWU(initMessages) &&
    distinctElementsInit(initMessages)
  }

  def areInChannelsInit1(): Boolean = {
    areInChannels(a1, List(a2,a3))
  } holds

  def areInChannelsInit2(): Boolean = {
    areInChannels(a2, List(a1,a3))
  } holds

  def areInChannelsInit3(): Boolean = {
    areInChannels(a3, List(a1,a2))
  } holds

  def areInChannelsBisInit1(): Boolean = {
    areInChannelsBis(List(a2,a3))
  } holds

  def areInChannelsBisInit2(): Boolean = {
    areInChannelsBis(List(a1,a3))
  } holds

  def areInChannelsBisInit3(): Boolean = {
    areInChannelsBis(List(a1,a2))
  } holds



  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: Map[ActorId, State], messages: Map[(ActorId,ActorId),List[Message]], getActor: Map[ActorId,Actor]) = {
    getActor.contains(a1) &&
    getActor.contains(a2) &&
    getActor.contains(a3) &&
    getActor.contains(a4) &&
    states.contains(a1) &&
    states.contains(a2) &&
    states.contains(a3) &&
    states.contains(a4) &&
    //messages(a4,a4).isEmpty &&
    getActor(a1) == SystemActor(a1, List(a2,a3)) &&
    getActor(a2) == SystemActor(a2, List(a1,a3)) &&
    getActor(a3) == SystemActor(a3, List(a1,a2)) &&
    areInChannels(a1, List(a2,a3)) &&
    areInChannels(a2, List(a1,a3)) &&
    areInChannels(a3, List(a1,a2)) &&
    areInChannelsBis(List(a2,a3)) &&
    areInChannelsBis(List(a1,a3)) &&
    areInChannelsBis(List(a1,a2)) &&
    distinctElements[ActorId](List(a1,a2)) &&
    distinctElements[ActorId](List(a1,a3)) &&
    distinctElements[ActorId](List(a2,a3)) &&
    distinctElements[ActorId](List(a1,a2,a3)) &&
    getActor(a4) == UserActor(a4) &&
    distinctChannels() &&
    WriteHistory(messages, states)  &&
    tableHistory(param, states) &&
    not2WriteUser(channels, messages)&&
    uniqueWriteUser(messages, channels) &&
    prop3(messages, channels) &&
    prop5(messages, channels) &&
    prop6(messages, channels) &&
    prop7(channels, messages) &&
    prop4(messages, states, channels, List(a1,a2,a3)) &&
    prop9(messages, channels) &&
    prop10(messages, channels) &&
    prop8(messages, states, channels) &&
   true
  }


  //basic functions
  def runActorsPrecondition(p: Parameter, initialActor: Actor, schedule: List[(ActorId,ActorId,Message)]) = {
    initialActor.myId == a4 &&
    validParam(p)
  }

  def userActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
     networkInvariant(net.param, net.states, net.messages, net.getActor) &&
     receiver.myId == a4 &&
     {
     val myId = receiver.myId
     (sender, m, receiver.state) match {
        case (sender, Value(v,idM,h), UserState(x,counter)) =>
          val newStates = net.states.updated(myId, UserState(Cons((idM,h),x), counter))
          (newStates(a4) == UserState(Cons((idM,h),x), counter)) &&
          ajoutUserCheckWriteForAll(channels, net.messages, x, (idM,h)) &&
          checkWriteForAll(channels, net.messages, Cons((idM,h), x)) &&
          addUserCheckTable(net.param, net.states, (idM, h)) &&
          updateStateUserProp4(net.messages, channels, net.states, myId, UserState(Cons((idM,h),x), counter), List(a1,a2,a3)) &&
          updateStateUserProp8(net.messages, net.states, channels, myId, UserState(Cons((idM,h),x), counter)) &&
          networkInvariant(net.param, newStates, net.messages, net.getActor)

        case (sender, AckUser(idM,h), UserState(x,counter)) =>
          val newStates = net.states.updated(myId, UserState(Cons((idM,h),x), counter))
          (newStates(a4) == UserState(Cons((idM,h),x), counter)) &&
          ajoutUserCheckWriteForAll(channels, net.messages, x, (idM,h)) &&
          checkWriteForAll(channels, net.messages, Cons((idM,h), x)) &&
          addUserCheckTable(net.param, net.states, (idM, h)) &&
          updateStateUserProp4(net.messages, channels, net.states, myId, UserState(Cons((idM,h),x), counter), List(a1,a2,a3)) &&
          updateStateUserProp8(net.messages, net.states, channels, myId, UserState(Cons((idM,h),x), counter)) &&
          networkInvariant(net.param, newStates, net.messages, net.getActor)
        case _ => true
     }
     } &&
     true
  }

  def addMessage(otherActor: List[ActorId], messages:Map[(ActorId, ActorId), List[Message]], m: Message, id: ActorId):Map[(ActorId, ActorId), List[Message]] = {
    require{
      m match {
        case WriteSystem(s,i,idM,h) => true
        case _ => false
      }
    }
    val WriteSystem(s,i,idM,h) = m
    otherActor match {
      case Nil() =>
        messages.updated((id,a4), messages.getOrElse((id,a4), Nil()) :+ AckUser(idM,h))
      case Cons(x,xs) =>
        val newMessages = messages.updated((id,x), messages.getOrElse((id,x), Nil()) :+ m)
        addMessage(xs, newMessages, m, id)
    }
  }

  def areInChannels(id: ActorId, l: List[ActorId]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x,xs) =>
        channels.contains((id,x)) &&
        areInChannels(id, xs)
    }
  }

  def areInChannelsBis(l: List[ActorId]): Boolean = {
    l match {
      case Nil() => true
      case Cons(x,xs) =>
        channels.contains((x,x)) &&
        areInChannelsBis(xs)
    }
  }

  def broadcastAckPre(
    receiver: Actor,
    otherActor: List[ActorId],
    m: Message,
    param: Parameter,
    states: Map[ActorId, State],
    messages: Map[(ActorId, ActorId), List[Message]],
    getActor: Map[ActorId, Actor]
  ): Boolean = {
    (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
     networkInvariant(param, states, messages, getActor) &&
     distinctElements[ActorId](otherActor) &&
    {
    receiver match {
      case SystemActor(_,_) => true
      case _ => false
    }
    } &&
    {
    val UserState(userHistory,c) = states(a4)
    m match {
      case WriteSystem(x,v,idM,h) =>
        userHistory.contains((idM,Set())) &&
        !collectWUsList(messages, channels).contains(WriteUser(x,v)) &&
        collectOtherActor(receiver.myId, otherActor, messages, WriteUser(x,v)) &&
        collectOtherActorProp7(otherActor, messages, WriteUser(x,v)) &&
        collectOtherActorProp9(otherActor, messages, WriteUser(x,v)) &&
        !collectWWsList(messages, channels).contains(WriteUser(x,v)) &&
        !allHistoriesContains_aux(x, v, otherActor, states) &&
        true
      case _ => false
    }
    } &&
    {
      broadcastAckPreBis(receiver, otherActor, m, param, states, messages, getActor)
    }
  }

  def broadcastAckPreBis(
    receiver: Actor,
    otherActor: List[ActorId],
    m: Message,
    param: Parameter,
    states: Map[ActorId, State],
    messages: Map[(ActorId, ActorId), List[Message]],
    getActor: Map[ActorId, Actor]
  ): Boolean = {
    require(
      distinctElements[ActorId](otherActor) &&
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(param, states, messages, getActor) &&
      {
      receiver match {
        case SystemActor(_,_) => true
        case _ => false
      }
      } &&
      {
      val UserState(userHistory,c) = states(a4)
      m match {
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(messages, channels).contains(WriteUser(x,v)) &&
          collectOtherActor(receiver.myId, otherActor, messages, WriteUser(x,v)) &&
          collectOtherActorProp7(otherActor, messages, WriteUser(x,v)) &&
          collectOtherActorProp9(otherActor, messages, WriteUser(x,v)) &&
          !collectWWsList(messages, channels).contains(WriteUser(x,v)) &&
          !allHistoriesContains_aux(x, v, otherActor, states)
        case _ => false
      }
      }
    )

    val myId = receiver.myId
    val UserState(userHistory,c) = states(a4)
    val WriteSystem(s,i,idM,h) = m

    otherActor match {
      case Nil() =>
        val newMessages = messages.updated((myId,a4), messages.getOrElse((myId,a4), Nil()) :+ AckUser(idM,h))
        addNot2WriteUser(channels, messages, myId, a4, AckUser(idM,h)) &&
        addUniqueWriteUser(messages, channels, (myId,a4), AckUser(idM,h)) &&
        (ajoutCheckWriteForAll( channels, messages, userHistory, AckUser(idM,h), myId, a4)) &&
        addOtherProp3(messages, channels, (myId,a4), AckUser(idM,h)) &&
        addOtherprop5(messages, channels, (myId,a4), AckUser(idM,h)) &&
        addOtherProp6(messages, channels, (myId,a4), AckUser(idM,h)) &&
        addProp7(messages, channels, (myId, a4), AckUser(idM,h)) &&
        addOtherProp4(messages, channels, states, (myId,a4), AckUser(idM,h), List(a1,a2,a3)) &&
        addOtherProp9(messages, channels, (myId,a4), AckUser(idM,h)) &&
        WriteHistory(newMessages, states)  &&
        addProp10(messages, channels, (myId, a4), AckUser(idM,h)) &&
        addOtherProp8(messages, states, channels, (myId, a4), AckUser(idM,h)) &&
        networkInvariant(param, states, newMessages, getActor) &&
        networkInvariant(param, states, addMessage(otherActor, messages, m, myId), getActor) &&
        true

      case Cons(x, xs) =>
        val newMessages = messages.updated((myId,x), messages.getOrElse((myId,x), Nil()) :+ m)
        addNot2WriteUser(channels, messages, myId, x, m) &&
        addUniqueWriteUser(messages, channels, (myId,x), m) &&
        (ajoutCheckWriteForAll(channels, messages, userHistory, m, myId, x)) &&
        addWSprop3(messages, channels, (myId,x), m) &&
        broadcastAckPreInduct(myId, otherActor, messages, m) &&
        broadcastAckPreInductProp7(myId, otherActor, messages, m) &&
        broadcastAckPreInductProp9(myId, otherActor, messages, m) &&
        addCollect3(messages, (myId, x), m, channels) &&
        addWSprop5(messages, channels, (myId,x), m) &&
        addOtherProp6(messages, channels, (myId,x), m) &&
        addProp7(messages, channels, (myId,x), m) &&
        addOtherProp4(messages, channels, states, (myId,x), m, List(a1,a2,a3)) &&
        addWSProp9(messages, channels, (myId,x), m) &&
        addProp10(messages, channels, (myId, x), m) &&
        addWSProp8(messages, states, channels, (myId,x), m, otherActor) &&
        WriteHistory(newMessages, states)  &&
        networkInvariant(param, states, newMessages, getActor) &&
        true
    }
  } holds


  def systemActorReceivePreCase1(
    receiver: Actor,
    sender: ActorId,
    m: Message
    )(implicit net: VerifiedNetwork): Boolean = {
    require{
      {
      receiver match {
        case SystemActor(_,otherActor) =>
          areInChannels(receiver.myId, otherActor) &&
          areInChannelsBis(otherActor) &&
          subsetOf(otherActor, List(a1,a2,a3)) &&
          !otherActor.contains(receiver.myId) &&
          true
        case _ => false
      }
      } &&
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      {
      val UserState(userHistory,c) = net.states(a4)
      (sender, m, receiver.state) match{
        case (id, WriteUser(s,i), CommonState(mem,h)) =>
          userHistory.contains(((true, s, i),Set())) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(s,i)) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(s,i)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(s,i)) &&
          !allHistoriesContains_aux(s, i, List(a1,a2,a3), net.states)
        case _ => false
      }
      }
    }

    //val UserState(userHistory,c) = net.states(a4)
    val myId = receiver.myId
    val SystemActor(_, otherActor) = receiver
    val WriteUser(s,i) = m
    val CommonState(mem,h) = receiver.state
    val idM = (true, s, i)

    val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set((true,s, i))))
    val variables = extractVariables(net.param)
    val UserState(newUserHistory,newc) = newStates(a4)
    newUserHistory.contains((true, s, i), Set()) &&
    updateCheckTable(net.param, net.states, s, i, myId) &&
    tableHistory(net.param, newStates) &&
    leMaprop5_2(myId, otherActor, net.messages, s, i) &&
    collectOtherActor(myId, otherActor, net.messages, WriteUser(s,i)) &&
    leMaprop7(myId, otherActor, net.messages, s, i) &&
    collectOtherActorProp7(otherActor, net.messages, WriteUser(s,i)) &&
    updateStateSystemProp4(net.messages, channels, net.states, myId, s, i, List(a1,a2,a3)) &&
    lemmaReceiveProp9(otherActor, net.messages, WriteUser(s,i)) &&
    collectOtherActorProp9(otherActor, net.messages, WriteUser(s,i))
    leMaprop8_2(net.messages, channels, myId, WriteUser(s,i)) &&
    updateStateSystemProp8(net.messages, net.states, channels, myId, s, i) &&
    leMaprop8_3(s,i,otherActor, List(a1,a2,a3), net.states, CommonState(mem.updated(s,i),h++Set((true,s, i))), myId) &&
    !allHistoriesContains_aux(s, i, otherActor, newStates) &&
    networkInvariant(net.param, newStates, net.messages, net.getActor) &&
    true
  }holds

  def systemActorReceivePreCase2(
    receiver: Actor,
    sender: ActorId,
    m: Message
    )(implicit net: VerifiedNetwork): Boolean = {
    require{
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      {
      val UserState(userHistory,c) = net.states(a4)
      m match {
        case WriteUser(x,v) =>
          userHistory.contains(((true, x, v),Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(x,v))
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v)) &&
          !collectWWs(net.messages.getOrElse((receiver.myId, receiver.myId), Nil())).contains(WriteUser(x,v))
        case WriteWaiting(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v)) &&
          !collectWWs(net.messages.getOrElse((receiver.myId, sender), Nil())).contains(WriteUser(x,v))
        case _ => true
      }
      } &&
      {
      (sender, m, receiver.state) match{
        case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) => true
        case _ => false
      }
      }
    }

    val UserState(userHistory,c) = net.states(a4)
    val myId = receiver.myId
    val id = sender
    val WriteSystem(s,i,idM,hs) = m
    val CommonState(mem,h) = receiver.state

    if (id != myId && (idM == (true, s, i))) {
      if (checkHistory(h,hs)){
        val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
        val UserState(newUserHistory,newc) = newStates(a4)
        (userHistory == newUserHistory) &&
        newUserHistory.contains((true, s, i), Set()) &&
        updateCheckTable(net.param, net.states, s, i, myId) &&
        tableHistory(net.param, newStates) &&
        WriteHistory(net.messages, newStates)  &&
        updateStateSystemProp4(net.messages, channels, net.states, myId, s, i, List(a1,a2,a3)) &&
        updateStateSystemProp8(net.messages, net.states, channels, myId, s, i) &&
        networkInvariant(net.param, newStates, net.messages, net.getActor)
      }
      else {
        val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
        (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
        WriteHistory(newMessages, net.states)  &&
        tableHistory(net.param, net.states) &&
        addNot2WriteUser(channels, net.messages, myId, myId, WriteWaiting(s,i,idM,hs)) &&
        addUniqueWriteUser(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp3(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherprop5(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addWWProp6(net.messages, channels, (myId, myId),
        WriteWaiting(s,i,idM,hs)) &&
        addProp7(net.messages, channels, (myId,myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp4(net.messages, channels, net.states, (myId, myId), WriteWaiting(s,i,idM,hs), List(a1,a2,a3)) &&
        addWWProp9(net.messages, channels, myId, WriteWaiting(s,i,idM,hs)) &&
        //theoremProp10(net.messages, channels, (myId, myId), s, i) &&
        addProp10(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp8(net.messages, net.states, channels, (myId,myId), WriteWaiting(s,i,idM,hs)) &&
        networkInvariant(net.param, net.states, newMessages, net.getActor)
      }
    }
    else {
      true
    }
  }holds

  def systemActorReceivePreCase3(
    receiver: Actor,
    sender: ActorId,
    m: Message
    )(implicit net: VerifiedNetwork): Boolean = {
    require{
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      {
      val UserState(userHistory,c) = net.states(a4)
      m match {
        case WriteUser(x,v) =>
          userHistory.contains(((true, x, v),Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(x,v))
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v))  &&
          !collectWWs(net.messages.getOrElse((receiver.myId, receiver.myId), Nil())).contains(WriteUser(x,v))
        case WriteWaiting(x,v,idM,h) if (receiver.myId == sender) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v))  &&
          !collectWWs(net.messages.getOrElse((receiver.myId, sender), Nil())).contains(WriteUser(x,v))
        case _ => true
      }
      } &&
      {
      (sender, m, receiver.state) match{
        case (id,WriteWaiting(s,i,idM,hs), CommonState(mem,h)) => true
        case _ => false
      }
      }
    }

    val UserState(userHistory,c) = net.states(a4)
    val myId = receiver.myId
    val id = sender
    val WriteWaiting(s,i,idM,hs) = m
    val CommonState(mem,h) = receiver.state

    if (id==myId && idM == (true, s, i)) {
      if (checkHistory(h,hs)){
        val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
        val UserState(newUserHistory,newc) = newStates(a4)
        (userHistory == newUserHistory) &&
        newUserHistory.contains((true, s, i), Set()) &&
        updateCheckTable(net.param, net.states, s, i, myId) &&
        tableHistory(net.param, newStates) &&
        WriteHistory(net.messages, newStates)  &&
        updateStateSystemProp4(net.messages, channels, net.states, myId, s, i, List(a1,a2,a3)) &&
        updateStateSystemProp8(net.messages, net.states, channels, myId, s, i) &&
        networkInvariant(net.param, newStates, net.messages, net.getActor)
      }
      else {
        val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
        (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
        WriteHistory(newMessages, net.states)  &&
        tableHistory(net.param, net.states) &&
        addNot2WriteUser(channels, net.messages, myId, myId, WriteWaiting(s,i,idM,hs)) &&
        addUniqueWriteUser(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp3(net.messages, channels, (myId, myId),
        WriteWaiting(s,i,idM,hs)) &&
        addOtherprop5(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addWWProp6(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addProp7(net.messages, channels, (myId,myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp4(net.messages, channels, net.states, (myId, myId), WriteWaiting(s,i,idM,hs), List(a1,a2,a3)) &&
        addWWProp9(net.messages, channels, myId, WriteWaiting(s,i,idM,hs)) &&
        //theoremProp10(net.messages, channels, (myId, myId), s, i) &&
        addProp10(net.messages, channels, (myId, myId), WriteWaiting(s,i,idM,hs)) &&
        addOtherProp8(net.messages, net.states, channels, (myId,myId), WriteWaiting(s,i,idM,hs)) &&
        networkInvariant(net.param, net.states, newMessages, net.getActor)
      }
    }
    else true
  }holds

  def systemActorReceivePreCase4(
    receiver: Actor,
    sender: ActorId,
    m: Message
    )(implicit net: VerifiedNetwork): Boolean = {
    require{
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      {
      val UserState(userHistory,c) = net.states(a4)
      m match {
        case WriteUser(x,v) =>
          userHistory.contains(((true, x, v),Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(x,v))
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v)) &&
          !collectWWs(net.messages.getOrElse((receiver.myId, receiver.myId), Nil())).contains(WriteUser(x,v))
        case WriteWaiting(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v))  &&
          !collectWWs(net.messages.getOrElse((receiver.myId, sender), Nil())).contains(WriteUser(x,v))
        case _ => true
      }
      } &&
      {
      (sender, m, receiver.state) match{
        case (id,Read(s), CommonState(mem,h)) => true
        case _ => false
      }
      }
    }

    val UserState(userHistory,c) = net.states(a4)
    val myId = receiver.myId
    val id = sender
    val Read(s) = m
    val CommonState(mem,h) = receiver.state
    val variables = extractVariables(net.param)

    if (id == a4 && {
          val variables = extractVariables(net.param)
          variables.contains(s)
          }) {
      val newMessages = net.messages.updated((myId,a4), net.messages.getOrElse((myId,a4), Nil()) :+ Value(mem.getOrElse(s,0),(false, s, mem.getOrElse(s,0)),h))
      tableHistory(net.param, net.states) &&
      tableToValue(s, variables, receiver.state, userHistory) &&
      ajoutCheckWriteForAll(channels, net.messages, userHistory, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h), myId, id) &&
      addNot2WriteUser(channels, net.messages, myId, id, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      WriteHistory(newMessages, net.states)  &&
      addUniqueWriteUser(net.messages, channels, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addOtherProp3(net.messages, channels, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addOtherprop5(net.messages, channels, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addOtherProp6(net.messages, channels, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addProp7(net.messages, channels, (myId,id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addOtherProp4(net.messages, channels, net.states, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h), List(a1,a2,a3)) &&
      addOtherProp9(net.messages, channels, (myId, id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addProp10(net.messages, channels, (myId,id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      addOtherProp8(net.messages, net.states, channels, (myId,id), Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      networkInvariant(net.param, net.states, newMessages, net.getActor) &&
      true
    }
    else true
  }holds



  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    require{
      receiver match {
        case SystemActor(_,otherActor) =>
          areInChannels(receiver.myId, otherActor) &&
          areInChannelsBis(otherActor) &&
          subsetOf(otherActor, List(a1,a2,a3)) &&
          !otherActor.contains(receiver.myId) &&
          true
        case _ => false
      }
    }

    val SystemActor(myId, otherActor) = receiver

    (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v) =>
          userHistory.contains(((true, x, v),Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !allHistoriesContains_aux(x, v, List(a1,a2,a3), net.states)
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v)) &&
          !collectWWs(net.messages.getOrElse((receiver.myId, receiver.myId), Nil())).contains(WriteUser(x,v))
        case WriteWaiting(x,v,idM,h) if (receiver.myId == sender) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(receiver.myId, channels, net.messages).contains(WriteUser(x,v))  &&
          !collectWWs(net.messages.getOrElse((receiver.myId, sender), Nil())).contains(WriteUser(x,v))
        case _ => true
    }} && {
    val UserState(userHistory,c) = net.states(a4)

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i), CommonState(mem,h)) =>
        !collectWUsList(net.messages, channels).contains(WriteUser(s,i)) &&
        !collectWSsList(net.messages, channels).contains(WriteUser(s,i)) &&
        systemActorReceivePreCase1(receiver, sender, m)

      case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) =>
        systemActorReceivePreCase2(receiver, sender, m)

      case (id,WriteWaiting(s,i,idM,hs), CommonState(mem,h)) =>
        systemActorReceivePreCase3(receiver, sender, m)

      case (id,Read(s), CommonState(mem,h)) =>
        systemActorReceivePreCase4(receiver, sender, m)

      case _ => true
      }
    }
  }

  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    validId(net, sender) &&
    validId(net, a.myId) &&
    net.states.contains(sender) &&
    net.states.contains(a.myId) &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v) =>
          userHistory.contains(((true, x, v),Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWSsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectWWsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !allHistoriesContains_aux(x, v, List(a1,a2,a3), net.states)
        case WriteSystem(x,v,idM,h) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(a.myId, channels, net.messages).contains(WriteUser(x,v))  &&
          !collectWWs(net.messages.getOrElse((a.myId, a.myId), Nil())).contains(WriteUser(x,v))
        case WriteWaiting(x,v,idM,h) if (a.myId == sender) =>
          userHistory.contains((idM,Set())) &&
          !collectWUsList(net.messages, channels).contains(WriteUser(x,v)) &&
          !collectNeighbour(a.myId, channels, net.messages).contains(WriteUser(x,v)) &&
          !collectWWs(net.messages.getOrElse((a.myId, sender), Nil())).contains(WriteUser(x,v))
        case _ => true
    }} && (
    a match {
      case UserActor(_) =>
        a.myId == a4 &&
        userActorReceivePre(a, sender, m)
      case SystemActor(myId,otherActor) =>
        (a.myId == a1 || a.myId == a2 || a.myId == a3) &&
        areInChannels(a.myId, otherActor) &&
        areInChannelsBis(otherActor) &&
        distinctElements(otherActor) &&
        subsetOf(otherActor, List(a1,a2,a3)) &&
        !otherActor.contains(a.myId) &&
        systemActorReceivePre(a, sender, m) &&
        true
    })
  }

  def peekMessageEnsuresReceivePre(n: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    require(networkInvariant(n.param, n.states, n.messages, n.getActor) && validId(n,sender) && validId(n,receiver))
    val sms = n.messages.getOrElse((sender,receiver), Nil())
    sms match {
      case Cons(x, xs) if (x == m) =>
        val messages2 = n.messages.updated((sender,receiver), xs);
          n.states(a4) match {
            case UserState(h,counter) =>
              inChannels(n, sender,receiver) &&
              removeCheckWriteForAll(channels, n.messages, h, sender, receiver) &&
              removeNot2WriteUser(n.messages, sender, receiver, channels) &&
              removeWU(n.messages, channels, (sender, receiver)) &&
              removeProp3(n.messages, (sender, receiver), channels)(n) &&
              inUserHistory(sender, receiver, n.messages, channels, h)&&
              checkWrite(sms, h) &&
              removeProp5(n.messages, channels, (sender, receiver)) &&
              removeProp6(n.messages, channels, (sender, receiver)) &&
              removeProp7(n.messages, channels, (sender, receiver)) &&
              removeProp4(n.messages, channels, n.states, (sender, receiver), List(a1,a2,a3)) &&
              removeProp9(n.messages, channels, (sender, receiver)) &&
              removeProp10(n.messages, channels, (sender, receiver)) &&
              removeProp8(n.messages, n.states, channels, List(a1,a2,a3), (sender, receiver)) &&
              prop3(messages2, channels) &&
              // m == WU : !collectWUsList(newMessages, channels).contains(WriteUser(s,i))
              // m == WU : !collectWSsList(newMessages, channels).contains(WriteUser(s,i))
              // m == WS :  !collectWUsList(newMessages, channels).contains(WriteUser(s,i))
              networkInvariant(n.param, n.states, messages2, n.getActor) &&
              true
            case _ =>
              inChannels(n, sender,receiver) &&
              removeNot2WriteUser(n.messages, sender, receiver, channels) &&
              removeWU(n.messages, channels, (sender, receiver)) &&
              removeProp3(n.messages, (sender, receiver), channels)(n) &&
              removeProp5(n.messages, channels, (sender, receiver)) &&
              removeProp6(n.messages, channels, (sender, receiver)) &&
              removeProp7(n.messages, channels, (sender, receiver)) &&
              removeProp4(n.messages, channels, n.states, (sender, receiver), List(a1,a2,a3)) &&
              prop3(messages2, channels) &&
              networkInvariant(n.param, n.states, messages2, n.getActor)
              true
          }

      case _ =>
        true
    }
  } holds

  def initBisPreBis(
    myId: ActorId,
    initList: List[(ActorId,Message)],
    net: VerifiedNetwork
  ): Boolean = {
    require(
      areWU(initList) &&
      myId == a4 &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) &&
      differentInitMessage(initList, net.messages) &&
      differentInitMessageWS(initList, net.messages) &&
      differentInitMessageWW(initList, net.messages) &&
      distinctElements[(ActorId,ActorId)](channels) &&
      {
        (init_states == net.states && inductInitProp4Empty(initList, List(a1,a2,a3))) ||
        inductInitProp4(initList, net.states, List(a1,a2,a3))
      } &&
      true
    )
    initList match {
        case Nil() => true
        case Cons((id, WriteUser(s,i)),xs) if(validId(net,id) && (id != a4)) =>
          val UserState(h,c) = net.states(myId)
          val newHistory: List[((Boolean, Variable, BigInt),Set[(Boolean,Variable, BigInt)])] = Cons(((true, s,i),Set()), h)
          val newStates = net.states.updated(a4,UserState(newHistory,c))
          val messages = net.messages.getOrElse((a4,id), Nil())
          val newMessages = net.messages.updated((a4,id),messages:+WriteUser(s,i))

          inChannels(net, a4, id) &&
          collectContains(net.messages, (a4,id), WriteUser(s,i)) &&
          !net.messages.getOrElse((a4,id), Nil()).contains(WriteUser(s,i)) &&
          ajoutUserCheckWriteForAll(channels, net.messages, h, ((true, s,i),Set())) &&
          ajoutCheckWriteForAll(channels, net.messages, newHistory, WriteUser(s, i), a4, id) &&
          addInitNot2WriteUser(channels, net.messages, a4,id, WriteUser(s, i)) &&
          addUserCheckTable(net.param, net.states, ((true,s,i), Set())) &&
          addUniqueWriteUserWU(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addWUprop3(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addOtherprop5(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addWUprop6(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addProp7(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addWUprop4(net.messages, channels, net.states, (a4,id), WriteUser(s,i), List(a1,a2,a3)) &&
          addOtherProp9(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addProp10(net.messages, channels, (a4,id), WriteUser(s,i)) &&
          addOtherProp8(net.messages, net.states, channels, (a4,id), WriteUser(s,i)) &&
          not2WriteUser(channels, newMessages) &&
          WriteHistory(newMessages, newStates)  &&
          tableHistory(net.param, newStates) &&
          not2WriteUser(channels, newMessages)&&
          uniqueWriteUser(newMessages, channels) &&
          prop4(newMessages, net.states, channels, List(a1,a2,a3)) &&
          updateStateUserProp4(newMessages, channels, net.states, a4, UserState(newHistory,c), List(a1,a2,a3)) &&
          updateStateUserProp8(newMessages, net.states, channels, a4, UserState(newHistory,c)) &&
          networkInvariant(net.param, newStates, newMessages, net.getActor) &&
          collectWUsList(net.messages, channels) ++Set(WriteUser(s,i)) == collectWUsList(newMessages, channels) &&
          removeDiff(initList, net.messages) &&
          differentInitMessage(xs, newMessages) &&
          differentInitMessageWS(xs, newMessages) &&
          differentInitMessageWW(xs, newMessages) &&
          updateInductInitProp4(initList, net.states, net.messages, List(a1,a2,a3)) &&
          true
        case _ => true
      }
    }holds

  def initBisPre(
    myId: ActorId,
    initList: List[(ActorId,Message)],
    net: VerifiedNetwork
  ): Boolean = {
    areWU(initList) &&
    myId == a4 &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    differentInitMessage(initList, net.messages) &&
    differentInitMessageWS(initList, net.messages) &&
    differentInitMessageWW(initList, net.messages) &&
    distinctElements[(ActorId,ActorId)](channels) &&
    {
    (init_states == net.states && inductInitProp4Empty(initList, List(a1,a2,a3))) ||
    inductInitProp4(initList, net.states, List(a1,a2,a3))
    } &&
    true
  }

  def initPre(
    myId: ActorId,
    initList: List[(ActorId,Message)],
    net: VerifiedNetwork
  ): Boolean = {
    areWU(initList) &&
    myId == a4 &&
    distinctElementsInit(initList) &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    net.messages == init_messages &&
    net.states == init_states &&
    initMessageEmpty() &&
    differentInitMessageEmpty(initList, net.messages) &&
    differentInitMessageWSEmpty(initList, net.messages) &&
    differentInitMessageWWEmpty(initList, net.messages) &&
    differentInitMessage(initList, net.messages) &&
    differentInitMessageWS(initList, net.messages) &&
    differentInitMessageWW(initList, net.messages) &&
    distinctChannels() &&
    distinctElements[(ActorId,ActorId)](channels)&&
    true
  }

  def initMessageEmpty(): Boolean = {
    collectWUsList(init_messages, channels).isEmpty &&
    collectWSsList(init_messages, channels).isEmpty &&
    collectWWsList(init_messages, channels).isEmpty
  }holds

  def differentInitMessageEmpty(
    initList: List[(ActorId, Message)],
    messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    require(distinctElementsInit(initList) && initMessageEmpty() && messages == init_messages)
    initList match {
      case Nil() => differentInitMessage(initList, messages)
      case Cons(x,xs) =>
        !newContains(x._2, xs) &&
        collectWUsList(messages, channels).isEmpty &&
        differentInitMessageEmpty(xs, messages) &&
        differentInitMessage(initList, messages)
    }
  }holds

  def differentInitMessageWSEmpty(
    initList: List[(ActorId, Message)],
    messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    require(distinctElementsInit(initList) && initMessageEmpty() && messages == init_messages)
    initList match {
      case Nil() => differentInitMessageWS(initList, messages)
      case Cons(x,xs) =>
        !newContains(x._2, xs) &&
        collectWSsList(messages, channels).isEmpty &&
        differentInitMessageWSEmpty(xs, messages) &&
        differentInitMessageWS(initList, messages)
    }
  }holds

  def differentInitMessageWWEmpty(
    initList: List[(ActorId, Message)],
    messages: Map[(ActorId,ActorId),List[Message]]): Boolean = {
    require(distinctElementsInit(initList) && initMessageEmpty() && messages == init_messages)
    initList match {
      case Nil() => differentInitMessageWW(initList, messages)
      case Cons(x,xs) =>
        !newContains(x._2, xs) &&
        collectWWsList(messages, channels).isEmpty &&
        differentInitMessageWWEmpty(xs, messages) &&
        differentInitMessageWW(initList, messages)
    }
  }holds

  def distinctChannels():Boolean = {
    distinctElements[(ActorId,ActorId)](channels)
  }holds

  def inUserHistory(
    sender: ActorId,
    receiver: ActorId,
    messages: Map[(ActorId,ActorId),List[Message]],
    channel: List[(ActorId,ActorId)],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]
    ): Boolean = {
    require(checkWriteForAll(channel, messages, userHistory) && channels.contains((sender,receiver)) &&
    channel.contains((sender,receiver)))

    val message = messages.getOrElse((sender,receiver), Nil())
    channel match {
      case Cons(x,xs) if (x==(sender,receiver)) => checkWrite(message, userHistory)
      case Cons(x,xs) => inUserHistory(sender,receiver,messages,xs, userHistory) && checkWrite(message,userHistory)
    }
  }holds

  def writeEmpty(states:Map[ActorId, State]) = {
    require(states.contains(a4) && {
      states(a4) match{
        case UserState(x,v) => true
        case _ => false
      }
    })
    val UserState(x,v) = states(a4)
    checkWriteForAllEmpty(channels, x) &&
    checkWriteForAll(channels, init_messages, x)
  }holds


  def checkEmpty(x:(ActorId, ActorId)): Boolean = {
    init_messages.getOrElse(x,Nil()).isEmpty
  }holds

  def checkWriteForAllEmpty(
    list: List[(ActorId,ActorId)],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]
    ): Boolean = {
    list match {
      case Nil() => checkWriteForAll(Nil(), init_messages, userHistory)
      case Cons(x,xs) =>
        checkEmpty(x) &&
        checkWrite(init_messages.getOrElse(x,Nil()), userHistory) &&
        checkWriteForAllEmpty(xs, userHistory) &&
        checkWriteForAll(xs, init_messages, userHistory)
    }
  }holds

  //function to prove WriteHistory
  def checkWrite(l: List[Message], userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(y,v) => userHistory.contains(((true, y, v),Set())) && checkWrite(q, userHistory)
          case WriteSystem(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case WriteWaiting(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case Value(v, idM, h) =>
            if (v != 0) {
              userHistory.contains(((true, idM._2, v),Set())) &&
              checkWrite(q, userHistory)
            }
            else {
              checkWrite(q, userHistory)
            }
          case _ => checkWrite(q, userHistory)
        }
    }
  }

  def checkWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]): Boolean = {

    list match {
      case Nil() => true
      case Cons((actor1,actor2), q) =>
        checkWrite(messages.getOrElse((actor1,actor2),Nil()), userHistory) && checkWriteForAll(q, messages, userHistory)
    }
  }

  // if there is a Write in a channel then there is the corresponding operation in the history of the User
  def WriteHistory(messages: Map[(ActorId,ActorId),List[Message]], states:Map[ActorId, State]): Boolean = {
    states.contains(a4) && {
    states(a4) match {
      case UserState(userHistory,c) =>
        checkWriteForAll(
          channels,
          messages,
          userHistory
        )
      case _ => false
    }
    }
  }

  @induct
  def ajoutCheckWrite(l: List[Message], m: Message, userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]):Boolean = {
    require {
      checkWrite(l, userHistory) && (
        m match {
          case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
          case Value(v, idM, h) =>
            if (v != 0) {
              userHistory.contains(((true, idM._2, v),Set()))
            }
            else true
          case _ => true
        })
    }

    checkWrite(l :+ m, userHistory)

  } holds

  @induct
  def removeCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    a1: ActorId, a2: ActorId
  ):Boolean = {
    require(checkWriteForAll(list, messages, userHistory))

    val ll = messages.getOrElse((a1,a2),Nil())

    ll match {
      case Nil() => true
      case Cons(x,xs) => checkWriteForAll(list, messages.updated((a1,a2), xs), userHistory)
    }
  } holds

  @induct
  def ajoutUserCheckWrite(
    l: List[Message],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    t: ((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])
  ):Boolean = {
    require(checkWrite(l, userHistory))

    checkWrite(l, Cons(t, userHistory))

  } holds

  def ajoutUserCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    t: ((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])
  ):Boolean = {
    require(checkWriteForAll(list, messages, userHistory))

    list match {
      case Nil() => checkWriteForAll(list, messages, Cons(t, userHistory))
      case Cons((b1,b2),q) =>
        ajoutUserCheckWrite(messages.getOrElse((b1,b2), Nil()), userHistory, t) &&
        ajoutUserCheckWriteForAll(q, messages, userHistory, t) &&
        checkWriteForAll(list, messages, Cons(t, userHistory))
    }
  } holds

//  @induct
  def ajoutCheckWriteForAll(
    list: List[(ActorId,ActorId)],
    messages: Map[(ActorId,ActorId),List[Message]],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    m: Message, a1: ActorId, a2: ActorId): Boolean = {
    require {
      checkWriteForAll(list, messages, userHistory) && (
        m match {
          case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
          case Value(v, idM, h) =>
            if (v != 0) {
              userHistory.contains(((true, idM._2, v),Set()))
            }
            else true
          case _ => true
        })
    }

    val ll = messages.getOrElse((a1,a2), Nil())
    val newMessages = messages.updated((a1,a2), ll :+ m)

    list match {
      case Nil() => checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
      case Cons((b1,b2),q) =>
        if (a1 == b1 && a2 == b2)
          ajoutCheckWrite(ll, m, userHistory) &&
          ajoutCheckWriteForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
        else
          checkWrite(newMessages.getOrElse((b1,b2), Nil()), userHistory) &&
          ajoutCheckWriteForAll(q, messages, userHistory, m, a1, a2) &&
          checkWriteForAll(list, messages.updated((a1,a2), ll :+ m), userHistory)
    }
  } holds






   //functions to prove tableHistory
  def tableHistory(param: Parameter, states: Map[ActorId, State]): Boolean = {
    states.contains(a1) &&
    states.contains(a2) &&
    states.contains(a3) &&
    states.contains(a4) && {
      val variables = extractVariables(param)
      states(a4) match {
        case UserState(userHistory,c) =>
          tableHistoryOne(variables, states(a1),userHistory) &&
          tableHistoryOne(variables, states(a2),userHistory) &&
          tableHistoryOne(variables, states(a3),userHistory)
        case _ => false
      }
    }
  }

  def tableHistoryOne(variables: List[Variable], state: State, userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]): Boolean = {
    state match {
      case CommonState(mem,h) =>
        variables match {
          case Nil() => true
          case Cons(x,xs) =>
            if (mem.getOrElse(x,0) != 0) {
              userHistory.contains((true, x, mem.getOrElse(x,0)), Set()) &&
              tableHistoryOne(xs, state, userHistory)
            }
            else {
              tableHistoryOne(xs, state, userHistory)
            }
        }
      case _ => false
    }
  }

  def addUserCheckTableOne(
    variables: List[Variable],
    state: State,
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    t: ((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])
    ): Boolean = {
    require(tableHistoryOne(variables, state, userHistory))
    variables match {
      case Nil() => true
      case Cons(x,xs) =>
        state match {
          case CommonState(mem,h) =>
            if (mem.getOrElse(x,0) != 0) {
              Cons(t, userHistory).contains((true, x, mem.getOrElse(x,0)), Set()) &&
              addUserCheckTableOne(xs, state, userHistory, t) &&
              tableHistoryOne(variables, state, Cons(t, userHistory))
            }
            else {
              addUserCheckTableOne(xs, state, userHistory, t) &&
              tableHistoryOne(variables, state, Cons(t, userHistory))
            }
          case _ => false
        }
    }
  }holds

  def addUserCheckTable(
    param: Parameter,
    states: Map[ActorId, State],
    t: ((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])
    ): Boolean = {
    require(tableHistory(param, states))
    val UserState(userHistory, c) = states(a4)
    val variables = extractVariables(param)
    addUserCheckTableOne(variables, states(a1), userHistory, t)&&
    addUserCheckTableOne(variables, states(a2), userHistory, t)&&
    addUserCheckTableOne(variables, states(a3), userHistory, t)
    tableHistory(param, states.updated(a4, UserState(Cons(t, userHistory),c)))
  }holds

  def updateCheckTable(
    param: Parameter,
    states: Map[ActorId, State],
    x: Variable,
    v: BigInt,
    id: ActorId
  ): Boolean = {
    require{
      (id == a1 || id == a2 || id == a3) &&
      tableHistory(param, states) && {
      val UserState(h,c) = states(a4)
      h.contains((true, x, v), Set())
      }
    }
    val UserState(userHistory, c) = states(a4)
    val variables = extractVariables(param)
    val CommonState(mem, h) = states(id)
    val newStates = states.updated(id, CommonState(mem.updated(x,v),h++Set((true, x, v))))
    updateCheckTableOne(variables, states(id), userHistory, x, v) &&
    tableHistory(param, newStates)
  }holds


  def updateCheckTableOne(
    variables: List[Variable],
    state: State,
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])],
    s: Variable,
    i: BigInt
    ): Boolean = {
    require(tableHistoryOne(variables, state, userHistory) && userHistory.contains((true, s, i), Set()))
    variables match {
      case Nil() => true
      case Cons(x,xs) =>
        val CommonState(mem,h) = state
        if (mem.getOrElse(x,0) != 0) {
           if (x==s) {
              mem.updated(s,i).getOrElse(x,0) == i &&
              userHistory.contains((true, x, mem.updated(s,i).getOrElse(x,0)), Set()) &&
              updateCheckTableOne(xs, state, userHistory, s, i) &&
              tableHistoryOne(variables, CommonState(mem.updated(s,i), h++Set((true, s, i))), userHistory)
            }
            else {
              mem.updated(s,i).getOrElse(x,0) == mem.getOrElse(x,0) &&
              userHistory.contains((true, x, mem.updated(s,i).getOrElse(x,0)), Set()) &&
              updateCheckTableOne(xs, state, userHistory, s, i) &&
              tableHistoryOne(variables, CommonState(mem.updated(s,i), h++Set((true, s, i))), userHistory)
            }
          }
      else {
        updateCheckTableOne(xs, state, userHistory, s, i) &&
        tableHistoryOne(variables, CommonState(mem.updated(s,i), h++Set((true, s, i))), userHistory)
      }
    }
  }holds

  def tableToValue(
    s: Variable,
    variables: List[Variable],
    state: State,
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]
    ): Boolean = {
    require(tableHistoryOne(variables, state, userHistory) && variables.contains(s))

    val CommonState(mem,h) = state

    variables match {
      case Cons(x, xs) if (x==s) =>
        if (mem.getOrElse(x,0) != 0) {
          userHistory.contains((true, s, mem.getOrElse(s,0)), Set())
        }
        else true
      case Cons(x, xs) =>
        tableToValue(s, xs, state, userHistory) &&
        {
          if(mem.getOrElse(s,0) != 0) {
            userHistory.contains((true, s, mem.getOrElse(s,0)), Set())
          }
          else true
        }
    }
  }holds

  def initTableHistory(param: Parameter, states: Map[ActorId, State]): Boolean = {
    require(states == init_states &&
    states.contains(a1) &&
    states.contains(a2) &&
    states.contains(a3) &&
    states.contains(a4))
      val variables = extractVariables(param)
      states(a4) match {
        case UserState(userHistory,c) =>
          initTableHistoryOne(variables, states(a1),userHistory) &&
          initTableHistoryOne(variables, states(a2),userHistory) &&
          initTableHistoryOne(variables, states(a3),userHistory) &&
          tableHistory(param, states)
        case _ => false
      }
  }holds

  def initTableHistoryOne(variables: List[Variable], state: State, userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]): Boolean = {
    require(state == CommonState(init_mem, Set()))
    state match {
      case CommonState(mem, h) =>
        variables match {
          case Nil() => true
          case Cons(x,xs) =>
            mem.getOrElse(x, 0) == 0 &&
            initTableHistoryOne(xs, state, userHistory) &&
            tableHistoryOne(variables, state, userHistory)
      }
      case _ => false
    }
  }holds


// property 1
  def not2WriteUser(
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        not2WriteUserOne(x._1, x._2, messages.getOrElse(x, Nil())) &&
        not2WriteUser(xs, messages)
    }
  }

  def not2WriteUserOne(
    id1: ActorId,
    id2: ActorId,
    messages: List[Message]
  ): Boolean = {
    messages match {
      case Nil() => true
      case Cons(x,xs) =>
        x match {
          case WriteUser(s,i) =>
            (!xs.contains(x)) &&
            not2WriteUserOne(id1,id2,xs)
          case _ =>
            not2WriteUserOne(id1,id2,xs)
        }
    }
  }

  def messagesEmpty(channels: List[(ActorId, ActorId)]): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        init_messages.getOrElse(x, Nil()).isEmpty &&
        not2WriteUserOne(x._1, x._2, init_messages.getOrElse(x, Nil())) &&
        messagesEmpty(xs) &&
        (collectWUs(init_messages.getOrElse(x,Nil())) & collectWUsList(init_messages,xs)).isEmpty &&
        uniqueWriteUser(init_messages, channels) &&
        not2WriteUser(channels, init_messages)
    }
  }holds

  def removeNot2WriteUser(
    messages: Map[(ActorId, ActorId), List[Message]],
    id1: ActorId,
    id2: ActorId,
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(
      not2WriteUser(channels, messages) &&
      {
        messages.getOrElse((id1,id2), Nil()) match {
          case Nil() => false
          case _ => true
        }
      }
    )
    val Cons(m,xs) = messages.getOrElse((id1,id2), Nil())
    val newMessages = messages.updated((id1,id2), xs)
    channels match {
      case Nil() => not2WriteUser(channels, newMessages)
      case Cons(x,xs) if(x == (id1,id2)) =>
        not2WriteUserOne(x._1, x._2, messages.getOrElse(x, Nil())) &&
        not2WriteUserOne(x._1, x._2, newMessages.getOrElse(x, Nil())) &&
        removeNot2WriteUser(messages, id1,id2, xs) &&
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) =>
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        not2WriteUserOne(x._1, x._2, newMessages.getOrElse(x, Nil())) &&
        removeNot2WriteUser(messages, id1,id2, xs) &&
        not2WriteUser(channels, newMessages)
    }
  } holds

  def addNot2WriteUser(
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId, ActorId), List[Message]],
    id1: ActorId,
    id2: ActorId,
    m: Message
  ): Boolean = {
  require(
    not2WriteUser(channels, messages) &&
    {
      m match {
        case WriteUser(s,i) => false
        case _ => true
      }
    }
  )
    val newMessages = messages.updated((id1,id2), messages.getOrElse((id1,id2), Nil()) :+ m)
    channels match {
      case Nil() => not2WriteUser(channels, newMessages)
      case Cons(x,xs) if (x == (id1,id2)) =>
        addNot2WriteUserOne(messages.getOrElse((id1,id2), Nil()), id1, id2, m) &&
        addNot2WriteUser(xs, messages, id1, id2, m) &&
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) =>
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        not2WriteUserOne(x._1, x._2, newMessages.getOrElse(x, Nil())) &&
        addNot2WriteUser(xs, messages, id1,id2, m) &&
        not2WriteUser(channels, newMessages)
    }
  }holds

  def addNot2WriteUserOne(
    messages: List[Message],
    id1: ActorId,
    id2: ActorId,
    m: Message
  ): Boolean = {
    require(
      not2WriteUserOne(id1,id2, messages) &&
      {
        m match {
          case WriteUser(s,i) => false
          case _ => true
        }
      })
    messages match {
      case Nil() =>
        not2WriteUserOne(id1, id2, List(m))
      case Cons(x,xs) =>
        addNot2WriteUserOne(xs,id1,id2, m) &&
        not2WriteUserOne(id1, id2, messages :+ m)
    }
  }holds


  def initMessagesContents(
    channels: List[(ActorId, ActorId)],
    messages: Map[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        initMessagesContentsOne(x, messages) &&
        true
    }
  }

  def initMessagesContentsOne(
    x: (ActorId, ActorId),
    messages: Map[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    if(x._1 != a4){
      messages.getOrElse(x, Nil()).isEmpty &&
      not2WriteUserOne(x._1, x._2, Nil())
    }
    else {
      true
    }
  }


  def addInitNot2WriteUserOne(
    messages: List[Message],
    m: Message,
    id1: ActorId,
    id2: ActorId
  ): Boolean = {
  require(
    not2WriteUserOne(id1,id2, messages) &&
    !messages.contains(m)
  )
    val newMessages = messages :+ m
    messages match {
      case Nil() =>
        not2WriteUserOne(id1,id2, newMessages)
      case Cons(x,xs) if (x == m) =>
        false
      case Cons(x,xs) =>
        addInitNot2WriteUserOne(xs, m, id1, id2) &&
        not2WriteUserOne(id1,id2, newMessages)
    }
  }holds

  def addInitNot2WriteUser(
    channels: List[(ActorId,ActorId)],
    messages: Map[(ActorId,ActorId), List[Message]],
    id1: ActorId,
    id2: ActorId,
    m: Message
  ): Boolean = {
  require(
    not2WriteUser(channels, messages) &&
    !messages.getOrElse((id1,id2), Nil()).contains(m)
  )
    val newMessages = messages.updated((id1,id2), messages.getOrElse((id1,id2), Nil()) :+ m)
    channels match {
      case Nil() =>
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) if (x == (id1,id2))=>
        addInitNot2WriteUserOne(messages.getOrElse((id1,id2), Nil()), m, id1, id2) &&
        not2WriteUserOne(id1,id2, newMessages.getOrElse((id1,id2), Nil())) &&
        addInitNot2WriteUser(xs, messages, id1, id2, m) &&
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        not2WriteUserOne(x._1,x._2, newMessages.getOrElse(x, Nil())) &&
        addInitNot2WriteUser(xs, messages, id1, id2, m) &&
        not2WriteUser(channels, newMessages)
    }
  }holds



//property 2
  def collectWUs(l: List[Message]): Set[Message] = {
    l match {
      case Nil() => Set()
      case Cons(x@WriteUser(s,i), xs) => collectWUs(xs) ++ Set(x)
      case Cons(_,xs) => collectWUs(xs)
    }
  }

  def collectWUsList(messages: Map[(ActorId,ActorId),List[Message]], channels: List[(ActorId,ActorId)]): Set[Message] = {
    channels match {
      case Nil() => Set()
      case Cons(c,cs) =>
        collectWUs(messages.getOrElse(c,Nil())) ++ collectWUsList(messages,cs)

    }
  }

  def uniqueWriteUser(messages: Map[(ActorId,ActorId),List[Message]], channels: List[(ActorId,ActorId)]): Boolean = {
    channels match {
      case Nil() => true
      case Cons(c,cs) =>
        (collectWUs(messages.getOrElse(c,Nil())) & collectWUsList(messages,cs)).isEmpty &&
        uniqueWriteUser(messages,cs)
    }
  }

  def add(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId,ActorId),
    m: Message
  ) = {
    messages.updated(c, messages.getOrElse(c, Nil()) :+ m)
  }

  @induct
  def addCollectOne(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteUser(s,i) => false
        case _ => true
      }
    })
    collectWUs(l) == collectWUs(l :+ m)
  } holds

  def addCollect(messages: Map[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteUser(s,i) => false
        case _ => true
      }
    })

    channels match {
      case Nil() => collectWUsList(messages,channels) == collectWUsList(add(messages, c, m), channels)
      case Cons(d,ds) =>
      	addCollect(messages, c, m, ds) &&
        addCollectOne(messages.getOrElse(d,Nil()), m) &&
        collectWUsList(messages,channels) == collectWUsList(add(messages, c, m), channels)
    }

  } holds

  def addUniqueWriteUser(messages: Map[(ActorId,ActorId),List[Message]], channels: List[(ActorId,ActorId)], c: (ActorId,ActorId), m: Message): Boolean = {
    require(uniqueWriteUser(messages,channels) && {
      m match {
        case WriteUser(s,i) => false
        case _ => true
      }
    })

    channels match {
      case Nil() => uniqueWriteUser(add(messages, c, m), channels)
      case Cons(d, ds) =>
        addCollect(messages,c,m,ds) &&
        addCollectOne(messages.getOrElse(d,Nil()), m) &&
        addUniqueWriteUser(messages,ds,c,m) &&
    	  uniqueWriteUser(add(messages, c,m),channels)
    }
  } holds


  @induct
  def addCollectOneWU(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteUser(s,i) => true
        case _ => false
      }
    })
    collectWUs(l) ++Set(m) == collectWUs(l :+ m)
  } holds

  def addCollectWU(messages: Map[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteUser(s,i) => true
        case _ => false
      }
    })

    channels match {
      case Nil() =>
        true
      case Cons(d,ds) =>
        addCollectWU(messages, c, m, ds) &&
        addCollectOneWU(messages.getOrElse(d,Nil()), m) &&
        {
          if (channels.contains(c)) {
            collectWUsList(messages,channels) ++Set(m) == collectWUsList(add(messages, c, m), channels)
          }
          else {
            collectWUsList(messages,channels) == collectWUsList(add(messages, c, m), channels)
          }
        }
    }
  } holds


  def addUniqueWriteUserWU(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId,ActorId),
    m: Message
  ): Boolean = {
    require(uniqueWriteUser(messages,channels) &&
      {
        m match {
          case WriteUser(s,i) => true
          case _ => false
        }
      } &&
      !collectWUsList(messages, channels).contains(m) &&
      distinctElements[(ActorId,ActorId)](channels)
    )

    channels match {
      case Nil() => uniqueWriteUser(add(messages, c, m), channels)

      case Cons(d, ds) =>
        addCollectWU(messages,c,m,ds) &&
        addCollectOneWU(messages.getOrElse(d,Nil()), m) &&
        addUniqueWriteUserWU(messages,ds,c,m) &&
    	  uniqueWriteUser(add(messages, c,m),channels)
    }
  } holds

  def removeCollectWU(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId,ActorId)
  ): Boolean = {
    require(!messages.getOrElse(c, Nil()).isEmpty)
    val Cons(x,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c,chan)
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        removeCollectWU(messages, xs, c) &&
        (collectWUsList(newMessages, channels) subsetOf collectWUsList(messages, channels))
    }
  }holds

  def removeWU(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId,ActorId)
  ): Boolean = {
    require(
      uniqueWriteUser(messages, channels) &&
      !messages.getOrElse(c,Nil()).isEmpty
    )
    val Cons(x,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c,chan)
    channels match {
      case Nil() => uniqueWriteUser(newMessages, channels)
      case Cons(x,xs) =>
        removeCollectWU(messages, channels, c) &&
        removeWU(messages, xs, c) &&
        uniqueWriteUser(newMessages,xs)
    }
  }holds



// property 3
// WW(id) in C(i,j) => pas de WS(id)
  def prop3(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    (collectWUsList(messages, channels) & collectWSsList(messages,channels)).isEmpty
  }

  def collectWSs(l: List[Message]): Set[Message] = {
    l match {
      case Nil() => Set()
      case Cons(x@WriteSystem(s,i,id,h), xs) => collectWSs(xs) ++ Set(WriteUser(s,i))
      case Cons(_,xs) => collectWSs(xs)
    }
  }

  def collectWSsList(messages: Map[(ActorId,ActorId),List[Message]], channels: List[(ActorId,ActorId)]): Set[Message] = {
    channels match {
      case Nil() => Set()
      case Cons(c,cs) =>
        collectWSs(messages.getOrElse(c,Nil())) ++ collectWSsList(messages,cs)
    }
  }

  def removeNot2WriteUserBis(
    messages: Map[(ActorId, ActorId), List[Message]],
    id1: ActorId,
    id2: ActorId,
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(
      not2WriteUser(channels, messages) &&
      {
        messages.getOrElse((id1,id2), Nil()) match {
          case Nil() => false
          case Cons(WriteUser(s,i), xs) =>
            val newMessages = messages.updated((id1,id2), xs)
            (channels.contains((id1,id2)) || !newMessages.getOrElse((id1, id2), Nil()).contains(WriteUser(s,i)))
          case _ => false
        }
      }
    )
    val Cons(WriteUser(s,i),xs) = messages.getOrElse((id1,id2), Nil())
    val newMessages = messages.updated((id1,id2), xs)
    channels match {
      case Nil() =>
        !newMessages.getOrElse((id1, id2), Nil()).contains(WriteUser(s,i)) &&
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) if(x == (id1,id2)) =>
        not2WriteUserOne(x._1, x._2, messages.getOrElse(x, Nil())) &&
        not2WriteUserOne(x._1, x._2, newMessages.getOrElse(x, Nil())) &&
        !newMessages.getOrElse((id1, id2), Nil()).contains(WriteUser(s,i)) &&
        removeNot2WriteUserBis(messages, id1,id2, xs) &&
        not2WriteUser(channels, newMessages)
      case Cons(x,xs) =>
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        not2WriteUserOne(x._1, x._2, newMessages.getOrElse(x, Nil())) &&
        removeNot2WriteUserBis(messages, id1,id2, xs) &&
        !newMessages.getOrElse((id1, id2), Nil()).contains(WriteUser(s,i)) &&
        not2WriteUser(channels, newMessages)
    }
  }holds

  def removeWUprop3(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)]
  )(implicit net: VerifiedNetwork): Boolean = {
    require(
      distinctElements[(ActorId, ActorId)](channels) &&
      channels.contains(c) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Nil() => false
          case Cons(WriteUser(s,i), xs) => true
          case _ => false
        }
      } &&
      uniqueWriteUser(messages, channels) &&
      not2WriteUser(channels, messages) &&
      prop3(messages, channels)
    )

    val Cons(WriteUser(s,i),newChannel) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChannel)

    channels match {
      case Nil() => true
      case Cons(x,xs) if(x==c) =>
        theorem(messages.getOrElse(c,Nil()),WriteUser(s,i)) &&
        !collectWUsList(messages, xs).contains(WriteUser(s,i)) &&
        removeNot2WriteUserBis(messages, c._1, c._2, channels) &&
        !newMessages.getOrElse(c,Nil()).contains(WriteUser(s,i)) &&
        equivTheorem(newMessages.getOrElse(c,Nil()), WriteUser(s,i)) &&
        lemma(messages, c, xs) &&
        !collectWUsList(newMessages, channels).contains(WriteUser(s,i)) &&
        removeCollectWS(messages, channels, c) &&
        removeCollectWU(messages, channels, c) &&
        prop3(newMessages, channels) &&
        true

      case Cons(x,xs) =>
        removeWUprop3(messages, c, xs) &&
        theorem2(c, xs, WriteUser(s,i), messages) &&
        !collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && {
        if (messages.getOrElse(x,Nil()).contains(WriteUser(s,i))){
          theorem(messages.getOrElse(x,Nil()), WriteUser(s,i))
          !collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && collectWUs(messages.getOrElse(x,Nil())).contains(WriteUser(s,i)) && false
        }
        else {
          !messages.getOrElse(x,Nil()).contains(WriteUser(s,i))
        }
        } &&
        equivTheorem(newMessages.getOrElse(x, Nil()), WriteUser(s,i))&&
        !collectWUsList(newMessages, channels).contains(WriteUser(s,i)) &&
        removeCollectWS(messages, channels, c) &&
        removeCollectWU(messages, channels, c) &&
        prop3(newMessages, channels)
    }
  } holds

  def theorem(l: List[Message], m: Message): Boolean = {
    if (isWU(m) && l.contains(m)){
      l match {
        case Nil() => false
        case Cons(x@WriteUser(s,i), xs) if(x==m) =>
          collectWUs(l).contains(m)
        case Cons(_,xs) =>
          theorem(xs,m) &&
          collectWUs(l).contains(m)
      }
    }
    else true
  }holds

  def equivTheorem(l: List[Message], m: Message): Boolean = {
    require(isWU(m) && !l.contains(m))
    l match {
      case Nil() => true
      case Cons(x, xs) if (x==m) => false
      case Cons(x,xs) =>
        (x != m) &&
        equivTheorem(xs,m) &&
        !collectWUs(l).contains(m)
    }
  }holds

  def lemma(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels :List[(ActorId, ActorId)]
  ): Boolean = {
    require(!channels.contains(c) && !messages.getOrElse(c,Nil()).isEmpty)

    val Cons(d,ds) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, ds)

    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c) =>
        false
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        collectWUs(newMessages.getOrElse(x, Nil())) == collectWUs(newMessages.getOrElse(x, Nil())) &&
        lemma(messages, c, xs) &&
        collectWUsList(messages, channels) == collectWUsList(newMessages, channels)

    }
  } holds

  def removeCollectWS(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId,ActorId)
  ): Boolean = {
    require(!messages.getOrElse(c, Nil()).isEmpty)
    val Cons(x,chan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c,chan)
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        removeCollectWS(messages, xs, c) &&
        (collectWSsList(newMessages, channels) subsetOf collectWSsList(messages, channels))
    }
  }holds

  def theorem2(
    c: (ActorId, ActorId),
    l: List[(ActorId,ActorId)],
    m: Message,
    messages: Map[(ActorId,ActorId),List[Message]]
  ): Boolean = {
    require(isWU(m) && messages.getOrElse(c,Nil()).contains(m) && l.contains(c))
    l match {
      case Nil() => false
      case Cons(x,xs) if (x==c) =>
        theorem(messages.getOrElse(c, Nil()), m) &&
        collectWUsList(messages, l).contains(m)
      case Cons(x,xs) =>
        theorem2(c,xs,m, messages) &&
        collectWUsList(messages, l).contains(m)
    }
  }holds

  def theorem3(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    m: Message
  ): Boolean = {
    require(
      channels.contains(c) &&
      collectWUs(messages.getOrElse(c, Nil())).contains(m)
    )
    channels match {
      case Cons(x,xs) if (x==c) =>
        collectWUsList(messages, channels).contains(m)
      case Cons(x,xs) =>
        theorem3(messages, c, channels, m) &&
        collectWUsList(messages, channels).contains(m)
    }
  } holds

  def theorem3WS(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    m: Message
  ): Boolean = {
    require(
      channels.contains(c) &&
      collectWSs(messages.getOrElse(c, Nil())).contains(m)
    )
    channels match {
      case Cons(x,xs) if (x==c) =>
        collectWSsList(messages, channels).contains(m)
      case Cons(x,xs) =>
        theorem3WS(messages, c, channels, m) &&
        collectWSsList(messages, channels).contains(m)
    }
  } holds

  def removeOtherprop3(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)]
  )(implicit net: VerifiedNetwork): Boolean = {
    require(
      {
        messages.getOrElse(c, Nil()) match {
          case Nil() => false
          case Cons(WriteUser(s,i), xs) => false
          case _ => true
        }
      } &&
      prop3(messages, channels)
    )

    val Cons(x,newChannel) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChannel)

    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        removeCollectWS(messages, channels, c) &&
        removeCollectWU(messages, channels, c) &&
        prop3(newMessages, channels)
    }
  } holds

  def removeProp3(
    messages: Map[(ActorId,ActorId),List[Message]],
    c: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)]
  )(implicit net: VerifiedNetwork): Boolean = {
    require(
      distinctElements[(ActorId, ActorId)](channels) &&
      channels.contains(c) &&
      uniqueWriteUser(messages, channels) &&
      not2WriteUser(channels, messages) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Nil() => false
          case Cons(x, xs) => true
        }
      } &&
      prop3(messages, channels)
    )

    val Cons(m, xs) = messages.getOrElse(c, Nil())

    m match {
      case WriteUser(s,i) =>
        removeWUprop3(messages, c, channels)
      case _ =>
        removeOtherprop3(messages, c, channels)
    }
  }holds

  @induct
  def addCollectOneWS(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteSystem(s,i, id, h) => true
        case _ => false
      }
    })
    val WriteSystem(s,i,id,h) = m
    collectWSs(l) ++Set(WriteUser(s,i)) == collectWSs(l :+ m)
  } holds

  def addCollectWS(messages: Map[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteSystem(s,i,id,h) => true
        case _ => false
      }
    })

    val WriteSystem(s,i,id,h) = m

    channels match {
      case Nil() =>
        true
      case Cons(d,ds) =>
        addCollectWS(messages, c, m, ds) &&
        addCollectOneWS(messages.getOrElse(d,Nil()), m) &&
        {
          if (channels.contains(c)) {
            collectWSsList(messages,channels) ++Set(WriteUser(s,i)) == collectWSsList(add(messages, c, m), channels)
          }
          else {
            collectWSsList(messages,channels) == collectWSsList(add(messages, c, m), channels)
          }
        }
    }
  } holds

  @induct
  def addCollect2One(l: List[Message], m: Message): Boolean = {
    require({
      m match {
        case WriteSystem(s,i,id,h) => false
        case _ => true
      }
    })
    collectWSs(l) == collectWSs(l :+ m)
  } holds

  def addCollect2(messages: Map[(ActorId,ActorId),List[Message]], c: (ActorId,ActorId), m: Message, channels: List[(ActorId,ActorId)]): Boolean = {
  require({
      m match {
        case WriteSystem(s,i,id,h) => false
        case _ => true
      }
    })

    channels match {
      case Nil() =>
        collectWSsList(messages,channels) == collectWSsList(add(messages, c, m), channels)
      case Cons(d,ds) =>
      	addCollect2(messages, c, m, ds) &&
        addCollect2One(messages.getOrElse(d,Nil()), m) &&
        collectWSsList(messages,channels) == collectWSsList(add(messages, c, m), channels)
    }

  } holds

  def addWSprop3(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      {
        m match {
          case WriteSystem(s,i,id,h) =>
            !collectWUsList(messages, channels).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    val newMessages = add(messages, c, m)
    val WriteSystem(s,i,id,h) = m

    addCollect(messages, c, m, channels) &&
    collectWUsList(newMessages, channels) == collectWUsList(messages, channels) &&
    !collectWUsList(newMessages, channels).contains(WriteUser(s,i))
    addCollectWS(messages, c, m, channels) &&
    collectWSsList(newMessages, channels).subsetOf(collectWSsList(messages, channels)++Set(WriteUser(s,i))) &&
    prop3(newMessages, channels)

  } holds

  def addOtherProp3(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      {
        m match {
          case WriteUser(s,i) => false
          case WriteSystem(s,i,id,h) => false
          case _ => true
        }
      }
    )
    val newMessages = add(messages, c, m)
    addCollect(messages, c, m, channels) &&
    collectWUsList(newMessages, channels) == collectWUsList(messages, channels) &&
    addCollect2(messages, c, m, channels) &&
    collectWSsList(newMessages, channels) == collectWSsList(messages, channels) &&
    prop3(newMessages, channels)

  } holds

  def addWUprop3(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId, ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      !collectWSsList(messages, channels).contains(m) &&
      {
        m match {
          case WriteUser(s,i) => true
          case _ => false
        }
      }
    )

    val newMessages = add(messages, c, m)

    addCollect2(messages, c, m, channels) &&
    addCollectWU(messages, c, m, channels) &&
    prop3(newMessages, channels)

  } holds


// property 5
// less than two WS
  def prop5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) =>
        prop5One(messages.getOrElse(x, Nil())) &&
        prop5(messages, xs)
    }
  }

  def prop5One(
    list: List[Message]
  ): Boolean = {
    list match {
      case Nil() => true
      case Cons(x@WriteSystem(s,i,id,h), xs) =>
        !collectWSs(xs).contains(WriteUser(s,i)) &&
        prop5One(xs)
      case Cons(x,xs) =>
        prop5One(xs)
    }
  }

  def removeProp5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      prop5(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty &&
      channels.contains(c)
    )
    val Cons(m,xs) = messages.getOrElse(c, Nil())

    m match {
      case WriteUser(s,i) =>
        removeAllProp5(messages, channels, c) &&
        removeWUprop5(messages, channels, c)
      case _ =>
        removeAllProp5(messages, channels, c)
    }
  } holds

  def removeAllProp5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop5(messages, channels) &&
      !messages.getOrElse(c, Nil()).isEmpty
    )

    val Cons(m,newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)

    channels match {
      case Nil() => true
      case Cons(x,xs) if(x==c) =>
        removeOneProp5(messages.getOrElse(x, Nil())) &&
        prop5One(newMessages.getOrElse(c, Nil())) &&
        removeAllProp5(messages, xs, c) &&
        prop5(newMessages, xs)
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop5One(messages.getOrElse(x, Nil())) &&
        removeAllProp5(messages, xs, c) &&
        prop5(newMessages, xs)
    }
  }holds

  def removeWUprop5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId)
  ): Boolean = {
    require(
      prop3(messages, channels) &&
      prop5(messages, channels) &&
      {
        messages.getOrElse(c, Nil()) match {
          case Cons(WriteUser(s,i), xs) => true
          case _ => false
        }
      } &&
      channels.contains(c)
    )
    val Cons(m, newChan) = messages.getOrElse(c, Nil())
    val newMessages = messages.updated(c, newChan)

    theorem(messages.getOrElse(c, Nil()), m) &&
    collectWUs(messages.getOrElse(c, Nil())).contains(m) &&
    theorem3(messages, c, channels, m) &&
    collectWUsList(messages, channels).contains(m) &&
    !collectWSsList(messages, channels).contains(m) &&
    removeCollectWS(messages, channels, c) &&
    !collectWSsList(newMessages, channels).contains(m)
  }holds

  def removeOneProp5(
    list: List[Message]
  ): Boolean = {
    require(prop5One(list) && !list.isEmpty)
    val Cons(x,xs) = list
    prop5One(xs)
  }holds

  def addWSprop5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop5(messages, channels) && {
        m match {
          case WriteSystem(s,i,id,h) =>
            !collectWSs(messages.getOrElse(c, Nil())).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    val newMessages = add(messages, c, m)

    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c) =>
        !collectWSs(messages.getOrElse(c, Nil())).contains(m)
        addWSprop5One(messages.getOrElse(c,Nil()), m) &&
        addWSprop5(messages, xs, c, m) &&
        prop5(newMessages, channels)
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop5One(newMessages.getOrElse(x, Nil())) &&
        addWSprop5(messages, xs, c, m) &&
        prop5(newMessages, channels) &&
        true
    }

  } holds

  def addWSprop5One(
    list: List[Message],
    m: Message
  ): Boolean = {
    require(
      prop5One(list) && {
        m match {
          case WriteSystem(s,i,id,h) =>
            !collectWSs(list).contains(WriteUser(s,i))
          case _ => false
        }
      }
    )
    list match {
      case Nil() =>
        prop5One(List(m))
      case Cons(x@WriteSystem(a,b,id,h),xs) =>
        !(x==m) &&
        !collectWSs(xs).contains(WriteUser(a,b)) &&
        addEnd(xs, m, x) &&
        !collectWSs(xs :+ m).contains(WriteUser(a,b)) &&
        addWSprop5One(xs, m) &&
        prop5One(list :+ m) &&
        true
      case Cons(x,xs) =>
        addWSprop5One(xs, m) &&
        prop5One(list :+ m) &&
        true
    }
  } holds

  def addEnd(
    list: List[Message],
    mAdded: Message,
    mHead: Message
    ): Boolean = {
    require(
      {
        mHead match {
          case WriteSystem(a,b,id,h) =>
            mAdded match {
              case WriteSystem(s,i,id,h) =>
                !collectWSs(list).contains(WriteUser(a,b)) &&
                !collectWSs(list).contains(WriteUser(s,i)) &&
                (a,b) != (s,i)
              case _ => false
            }
          case _ => false
        }
      }
    )
    val WriteSystem(a,b,id,h) = mHead

    list match {
      case Nil() =>
        !collectWSs(list :+ mAdded).contains(WriteUser(a,b))
      case Cons(x,xs) =>
        (x != mHead) &&
        addEnd(xs, mAdded, mHead) &&
        !collectWSs(list :+ mAdded).contains(WriteUser(a,b))
    }

  } holds

  def addOtherprop5(
    messages: Map[(ActorId,ActorId),List[Message]],
    channels: List[(ActorId,ActorId)],
    c: (ActorId, ActorId),
    m: Message
  ): Boolean = {
    require(
      prop5(messages, channels) && {
        m match {
          case WriteSystem(s,i,id,h) => false
          case _ => true
        }
      }
    )
    val newMessages = messages.updated(c, messages.getOrElse(c, Nil()) :+ m)

    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==c) =>
        newMessages.getOrElse(c, Nil()) == messages.getOrElse(c, Nil()) :+ m &&
        addCollect2One(messages.getOrElse(c, Nil()), m) &&
        addOtherprop5One(messages.getOrElse(c, Nil()), m) &&
        prop5One(newMessages.getOrElse(c, Nil())) &&
        addOtherprop5(messages, xs, c, m) &&
        prop5(newMessages, channels) &&
        true
      case Cons(x,xs) =>
        newMessages.getOrElse(x, Nil()) == messages.getOrElse(x, Nil()) &&
        prop5One(newMessages.getOrElse(x, Nil())) &&
        addOtherprop5(messages, xs, c, m) &&
        prop5(newMessages, channels) &&
        true
    }

  } holds

  def addOtherprop5One(
    list: List[Message],
    m: Message
  ): Boolean = {
    require(
      prop5One(list) &&
      !isWS(m)
    )

    list match {
      case Nil() => true
      case Cons(x@WriteSystem(s,i,id,h), xs) =>
        addCollect2One(xs, m) &&
        collectWSs(xs :+ m) == collectWSs(xs) &&
        !collectWSs(xs :+ m).contains(WriteUser(s,i)) &&
        addOtherprop5One(xs, m) &&
        prop5One(list :+ m) &&
        true
      case Cons(x,xs) =>
        addOtherprop5One(xs, m) &&
        prop5One(list :+ m) &&
        true
    }
  } holds

  def initProp5(
    messages: Map[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    require(collectWSsList(messages, channels).isEmpty)

    channels match {
      case Nil() => prop5(messages, channels)
      case Cons(x,xs) =>
        init_messages.getOrElse(x, Nil()).isEmpty &&
        initProp5One(messages.getOrElse(x, Nil())) &&
        prop5One(messages.getOrElse(x, Nil())) &&
        initProp5(messages, xs) &&
        prop5(messages, channels) &&
        true
    }
  }holds

  def initProp5One(
    list: List[Message]
  ): Boolean = {
    require(collectWSs(list).isEmpty)

    list match {
      case Nil() => true
      case Cons(x@WriteSystem(s,i,id,h), xs) =>
        !collectWSs(xs).contains(WriteUser(s,i)) &&
        initProp5One(xs) &&
        prop5One(list)
      case Cons(x,xs) =>
        initProp5One(xs)
        prop5One(list)
    }
  }holds

  def collectOtherActor(
    id: ActorId,
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message
  ): Boolean = {
    otherActor match {
      case Nil() => true
      case Cons(x,xs) =>
        !collectWSs(messages.getOrElse((id,x), Nil())).contains(m) &&
        collectOtherActor(id, xs, messages, m)
    }
  }

   def leMaprop5_2(
    id: ActorId,
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    s: Variable, i: BigInt
  ): Boolean = {
    require (
      areInChannels(id, otherActor) &&
      !collectWSsList(messages, channels).contains(WriteUser(s,i))
    )

    otherActor match {
      case Nil() => true
      case Cons(x,xs) =>
        collectOtherActorOne(id,x,messages,WriteUser(s,i),channels) &&
        !collectWSs(messages.getOrElse((id,x), Nil())).contains(WriteUser(s,i)) &&
        leMaprop5_2(id, xs, messages, s, i) &&
        collectOtherActor(id, otherActor, messages, WriteUser(s,i))
    }
   }holds

  def collectOtherActorOne(
    id: ActorId,
    id2: ActorId,
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message,
    channels : List[(ActorId, ActorId)]
  ): Boolean = {
    require(
      !collectWSsList(messages, channels).contains(m) &&
      channels.contains(id,id2)
    )
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x == (id,id2)) =>
        !collectWSs(messages.getOrElse((id,id2), Nil())).contains(m)
      case Cons(x,xs) =>
        collectOtherActorOne(id,id2,messages,m,xs) &&
        !collectWSs(messages.getOrElse((id,id2), Nil())).contains(m)
    }
  } holds

  def broadcastAckPreInduct(
    id: ActorId,
    otherActor: List[ActorId],
    messages: Map[(ActorId, ActorId), List[Message]],
    m: Message
  ): Boolean = {
    require(
      m match {
        case WriteSystem(s,i,idM,h) =>
          collectOtherActor(id, otherActor, messages, WriteUser(s,i)) &&
          distinctElements[ActorId](otherActor)
        case _ => false
      }
    )
    val WriteSystem(s,i,idM,h) = m

    otherActor match {
      case Nil() => true
      case Cons(x,Nil()) =>
        collectOtherActor(id, Nil(), add(messages, (id,x), m), WriteUser(s,i))
      case Cons(x,Cons(y,ys)) =>
        add(messages, (id,x), m).getOrElse((id,y), Nil()) == messages.getOrElse((id,y), Nil()) &&
        broadcastAckPreInduct(id, Cons(x,ys), messages, m) &&
        collectOtherActor(id, Cons(y,ys), add(messages, (id,x), m), WriteUser(s,i))
    }
  } holds

}










