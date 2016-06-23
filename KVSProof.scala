package distribution


import FifoNetwork._
import Networking._
import Protocol._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps


// This object contains lemma and auxiliary functions used in the proofs

object ProtocolProof {
  import Protocol._
  import PrettyPrinting._
  
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

  val init_mem = MMap[Variable, BigInt](
    Map[Variable, BigInt]()
  )
  
  val init_param = Variables(correct_variables)
  
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
  val init_messages1 = MMap.makeMap[(ActorId,ActorId),List[Message]](init_messages_list)
  val init_messages = init_messages1.updated((a4,a4), Nil())
  */
  
  
//   val init_states_list = List[(ActorId, State)](
//     (a1,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
//     (a2,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
//     (a3,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
//     (a4,UserState(Nil(),0))
//     )
//   val init_states = MMap.makeMap[ActorId,State](init_states_list)
  
  val init_states = MMap[ActorId, State](
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
//   val init_getActor = MMap.makeMap[ActorId,Actor](init_getActor_list)

  val init_getActor = MMap[ActorId, Actor](
    Map[ActorId, Actor](
      (a1,SystemActor(a1, List(a2,a3))),
      (a2,SystemActor(a2, List(a1,a3))),
      (a3,SystemActor(a3, List(a1,a2))),
      (a4,UserActor(a4))
    )
  )
  
  val init_messages = MMap[(ActorId, ActorId), List[Message]](
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
  
  def checkContent[A,B](l: List[(A,B)], m: MMap[A,B]): Boolean  = {
    l match {
      case Nil() => true
      case Cons((x,v), xs) => m.contains(x) && checkContent(xs, m)
    }
  }
  
  def makeNetwork(p: Parameter) = {
  
    VerifiedNetwork(init_param,
		init_states, 
		init_messages,
		init_getActor
		)
  }ensuring(res => 
    writeEmpty(res.states) && 
    WriteHistory(res.messages, res.states) && 
    //checkContent(init_states_list, init_states) && 
    //checkContent(init_getActor_list, init_getActor) &&
    res.getActor(a1) == SystemActor(a1, List(a2,a3)) &&
    res.getActor(a2) == SystemActor(a2, List(a1,a3)) &&
    res.getActor(a3) == SystemActor(a3, List(a1,a2)) &&
    res.getActor(a4) == UserActor(a4) && 
    messagesEmpty(channels) &&
    networkInvariant(res.param,res.states, res.messages, res.getActor) &&
    true
  )
  
  
  def validParam(p: Parameter): Boolean = {
    val Variables(variables) = p
    variables == correct_variables
  }
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
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
    getActor(a4) == UserActor(a4) && 
    WriteHistory(messages, states)  &&
    tableHistory(param, states) &&
    not2WriteUser(channels, messages)&&
    uniqueWriteUser(channels, messages) &&
    true
  }
  
  
  //basic functions
  def runActorsPrecondition(p: Parameter, initial_actor: Actor, schedule: List[(ActorId,ActorId,Message)]) = {
    initial_actor.myId == a4
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
          networkInvariant(net.param, newStates, net.messages, net.getActor)
        
        case (sender, AckUser(idM,h), UserState(x,counter)) => 
          val newStates = net.states.updated(myId, UserState(Cons((idM,h),x), counter))
          (newStates(a4) == UserState(Cons((idM,h),x), counter)) &&
          ajoutUserCheckWriteForAll(channels, net.messages, x, (idM,h)) &&
          checkWriteForAll(channels, net.messages, Cons((idM,h), x)) &&
          addUserCheckTable(net.param, net.states, (idM, h)) &&
          networkInvariant(net.param, newStates, net.messages, net.getActor)
        case _ => true
     }
     } &&
     true
  }
  
  def addMessage(otherActor: List[ActorId], messages:MMap[(ActorId, ActorId), List[Message]], m: Message, id: ActorId):MMap[(ActorId, ActorId), List[Message]] = {
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
  
  
  def broadcastAckPre(receiver: Actor, 
  otherActor: List[ActorId], 
  m: Message, 
  param: Parameter, 
  states: MMap[ActorId, State], 
  messages: MMap[(ActorId, ActorId), List[Message]], 
  getActor: MMap[ActorId, Actor]
  ): Boolean = {
    //require{
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
      case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
      case _ => false
    }
    } &&
   {
    val myId = receiver.myId
    val UserState(userHistory,c) = states(a4)
    val WriteSystem(s,i,idM,h) = m
    
    otherActor match {
      case Nil() => 
        val newMessages = messages.updated((myId,a4), messages.getOrElse((myId,a4), Nil()) :+ AckUser(idM,h))
        addNot2WriteUser(channels, messages, myId, a4, AckUser(idM,h)) &&
        addUniqueWriteUnser(channels, messages, AckUser(idM,h), (myId, a4)) &&
        (ajoutCheckWriteForAll(channels, messages, userHistory, AckUser(idM,h), myId, a4)) &&
        WriteHistory(newMessages, states)  &&
        networkInvariant(param, states, newMessages, getActor) &&
        networkInvariant(param, states, addMessage(otherActor, messages, m, myId), getActor) &&
        true
        
      case Cons(x, xs) => 
        val newMessages = messages.updated((myId,x), messages.getOrElse((myId,x), Nil()) :+ m)
        addNot2WriteUser(channels, messages, myId, x, m) &&
        addUniqueWriteUnser(channels, messages, m, (myId, x)) &&
        (ajoutCheckWriteForAll(channels, messages, userHistory, m, myId, x)) &&
        WriteHistory(newMessages, states)  &&
        networkInvariant(param, states, newMessages, getActor) &&
        true
    }
    }
  }
  
  def systemActorReceivePreCase1(
    receiver: Actor, 
    sender: ActorId, 
    m: Message
    )(implicit net: VerifiedNetwork): Boolean = {
    require{
      {
      receiver match {
        case SystemActor(_,_) => true
        case _ => false
      }
      } &&  
      (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
      networkInvariant(net.param, net.states, net.messages, net.getActor) && 
      {
      val UserState(userHistory,c) = net.states(a4)
      (sender, m, receiver.state) match{
        case (id, WriteUser(s,i), CommonState(mem,h)) => 
          userHistory.contains(((true, s, i),Set()))
        case _ => false
      }
      }
    }
  
    //val UserState(userHistory,c) = net.states(a4)
    val myId = receiver.myId
    val WriteUser(s,i) = m
    val CommonState(mem,h) = receiver.state
    val idM = (true, s, i)
    
    val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set((true,s, i))))
    val Variables(variables) = net.param
    val UserState(newUserHistory,newc) = newStates(a4)
    newUserHistory.contains((true, s, i), Set()) &&
    updateCheckTable(net.param, net.states, s, i, myId) &&
    tableHistory(net.param, newStates) &&
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
        case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
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
        networkInvariant(net.param, newStates, net.messages, net.getActor)
      }
      else {
        val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
        (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
        WriteHistory(newMessages, net.states)  &&
        tableHistory(net.param, net.states) &&
        addNot2WriteUser(channels, net.messages, myId, myId, WriteWaiting(s,i,idM,hs)) &&
        addUniqueWriteUnser(channels, net.messages, WriteWaiting(s,i,idM,hs), (myId, myId)) &&
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
        case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
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
    
    if (idM == (true, s, i)) {
      if (checkHistory(h,hs)){
        val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
        val UserState(newUserHistory,newc) = newStates(a4)
        (userHistory == newUserHistory) &&
        newUserHistory.contains((true, s, i), Set()) &&
        updateCheckTable(net.param, net.states, s, i, myId) &&
        tableHistory(net.param, newStates) &&
        WriteHistory(net.messages, newStates)  &&
        networkInvariant(net.param, newStates, net.messages, net.getActor)
      }
      else {
        val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
        (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
        WriteHistory(newMessages, net.states)  &&
        tableHistory(net.param, net.states) &&
        addNot2WriteUser(channels, net.messages, myId, myId, WriteWaiting(s,i,idM,hs)) &&
        addUniqueWriteUnser(channels, net.messages, WriteWaiting(s,i,idM,hs), (myId, myId)) &&
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
        case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
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
    val Variables(variables) = net.param
    
    if (id == a4 && {
          val Variables(variables) = net.param
          variables.contains(s)
          }) {
      val newMessages = net.messages.updated((myId,a4), net.messages.getOrElse((myId,a4), Nil()) :+ Value(mem.getOrElse(s,0),(false, s, mem.getOrElse(s,0)),h))
      tableHistory(net.param, net.states) &&
      tableToValue(s, variables, receiver.state, userHistory) &&
      ajoutCheckWriteForAll(channels, net.messages, userHistory, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h), myId, id) &&
      addNot2WriteUser(channels, net.messages, myId, id, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h)) &&
      WriteHistory(newMessages, net.states)  &&
      addUniqueWriteUnser(channels, net.messages, Value(mem.getOrElse(s,0), (false, s, mem.getOrElse(s,0)), h), (myId, id)) &&
      networkInvariant(net.param, net.states, newMessages, net.getActor)
    }
    else true
  }holds
  
  
  
  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    require{
      receiver match {
        case SystemActor(_,_) => true
        case _ => false
      }
    }
    val SystemActor(myId, otherActor) = receiver
    
    (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) && 
    {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }} && {
    val UserState(userHistory,c) = net.states(a4)

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i), CommonState(mem,h)) => 
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
    networkInvariant(net.param, net.states, net.messages, net.getActor) && {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v) => userHistory.contains(((true, x, v),Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }} && (
    a match {
      case UserActor(_) => userActorReceivePre(a, sender, m)
      case SystemActor(_,_) => systemActorReceivePre(a, sender, m)
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
              removeCheckWriteForAll(channels, n.messages, h, sender, receiver) &&
              removeNot2WriteUser(n.messages, sender, receiver, channels) &&
              inChannels(n, sender,receiver)&&
              inUserHistory(sender, receiver, n.messages, channels, h)&&
              checkWrite(sms, h) &&
              networkInvariant(n.param, n.states, messages2, n.getActor) &&
              true
            case _ => 
              removeNot2WriteUser(n.messages, sender, receiver, channels) &&
              networkInvariant(n.param, n.states, messages2, n.getActor)
          }
 
      case _ => 
        true
    }
  } holds

  def initPre(myId: ActorId, net: VerifiedNetwork): Boolean = {
    //require(
    myId == a4 && 
    networkInvariant(net.param, net.states, net.messages, net.getActor) &&
    net.messages == init_messages && 
    {
    val UserState(h,c) = net.states(myId)
    val newHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])] = Cons(((true, Variable(1),1),Set()), h)
    val newStates = net.states.updated(a4,UserState(newHistory,c+1))
    val messages = net.messages.getOrElse((a4,a1), Nil())
    val newMessages = net.messages.updated((a4,a1),messages:+WriteUser(Variable(1),1))
    
    ajoutUserCheckWriteForAll(channels, net.messages, h, ((true, Variable(1),1),Set())) &&
    networkInvariant(net.param, newStates, net.messages, net.getActor) &&
    ajoutCheckWriteForAll(channels, net.messages, newHistory, WriteUser(Variable(1), 1), a4, a1) && 
    addInitNot2WriteUser(channels, net.messages, a4,a1, WriteUser(Variable(1), 1)) &&
    not2WriteUser(channels, newMessages) &&
    networkInvariant(net.param, newStates, newMessages, net.getActor) &&
    true
    }
  }
  
  def inUserHistory(
    sender: ActorId, 
    receiver: ActorId, 
    messages: MMap[(ActorId,ActorId),List[Message]],
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
  
  def writeEmpty(states:MMap[ActorId, State]) = {
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
    messages: MMap[(ActorId,ActorId),List[Message]],
    userHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])]): Boolean = {

    list match {
      case Nil() => true
      case Cons((actor1,actor2), q) =>
        checkWrite(messages.getOrElse((actor1,actor2),Nil()), userHistory) && checkWriteForAll(q, messages, userHistory)
    }
  }
  
  // if there is a Write in a channel then there is the corresponding operation in the history of the User
  def WriteHistory(messages: MMap[(ActorId,ActorId),List[Message]], states:MMap[ActorId, State]): Boolean = {  
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
    messages: MMap[(ActorId,ActorId),List[Message]],
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
    messages: MMap[(ActorId,ActorId),List[Message]],
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
    messages: MMap[(ActorId,ActorId),List[Message]],
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
  def tableHistory(param: Parameter, states: MMap[ActorId, State]): Boolean = {    
    states.contains(a1) &&
    states.contains(a2) &&
    states.contains(a3) &&
    states.contains(a4) && { 
      val Variables(variables) = param
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
    states: MMap[ActorId, State],
    t: ((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])
    ): Boolean = {
    require(tableHistory(param, states))
    val UserState(userHistory, c) = states(a4)
    val Variables(variables) = param
    addUserCheckTableOne(variables, states(a1), userHistory, t)&&
    addUserCheckTableOne(variables, states(a2), userHistory, t)&&
    addUserCheckTableOne(variables, states(a3), userHistory, t)
    tableHistory(param, states.updated(a4, UserState(Cons(t, userHistory),c)))
  }holds
  
  def updateCheckTable(
    param: Parameter, 
    states: MMap[ActorId, State],
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
    val Variables(variables) = param
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
  
  
// property 1
  def not2WriteUser(
    channels: List[(ActorId, ActorId)],
    messages: MMap[(ActorId, ActorId), List[Message]]
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
        not2WriteUser(channels, init_messages)
    }
  }holds
  
  def removeNot2WriteUser(
    messages: MMap[(ActorId, ActorId), List[Message]], 
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
    val Cons(_,xs) = messages.getOrElse((id1,id2), Nil())
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
  }holds
  
  def addNot2WriteUser(
    channels: List[(ActorId, ActorId)],
    messages: MMap[(ActorId, ActorId), List[Message]],
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
    messages: MMap[(ActorId, ActorId), List[Message]]
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
    messages: MMap[(ActorId, ActorId), List[Message]]
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
    messages: MMap[(ActorId,ActorId), List[Message]], 
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
  def uniqueWriteUser(
    channels: List[(ActorId, ActorId)], 
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) => 
        uniqueWriteUserOne(x, messages.getOrElse(x, Nil()), messages, channels) &&
        uniqueWriteUser(xs, messages)
    }
  }

  def uniqueWriteUserOne(
    pair: (ActorId, ActorId),
    channelMessages: List[Message], 
    messages: MMap[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)]
  ): Boolean = {
    channelMessages match {
      case Nil() => true
      case Cons(WriteUser(s,i), xs) =>
        channelNotContains(WriteUser(s,i), pair, channels, messages) &&
        uniqueWriteUserOne(pair, xs, messages, channels)
      case Cons(x,xs) => 
        uniqueWriteUserOne(pair, xs, messages, channels)
    }
  }
  
  def channelNotContains(
    m: Message,
    pair: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    messages: MMap[(ActorId, ActorId), List[Message]]   
  ): Boolean = {
    channels match {
      case Nil() => true
      case Cons(x,xs) if (x==pair) => 
        channelNotContains(m,pair,xs,messages)
      case Cons(x,xs) =>
        !messages.getOrElse(x, Nil()).contains(m) &&
        channelNotContains(m,pair,xs,messages)
    }
  }
  
  def addUniqueWriteUnser(
    channels: List[(ActorId, ActorId)], 
    messages: MMap[(ActorId, ActorId), List[Message]], 
    m: Message,
    pair: (ActorId, ActorId)
  ): Boolean = {
  require(
    uniqueWriteUser(channels, messages) &&
    {
      m match {
        case WriteUser(s,i) => false
        case _ => true
      }
    }
  )
    val newMessages = messages.updated(pair, messages.getOrElse(pair, Nil()) :+ m)
    channels match {
      case Nil() => uniqueWriteUser(channels, newMessages)
      case Cons(x,xs) if (x==pair) =>
         addUniqueWriteUnserOne(pair, messages.getOrElse(pair, Nil()), messages, channels, m) &&
         addUniqueWriteUnser(xs, messages, m, pair) &&
         uniqueWriteUser(channels, newMessages)&&
        true
      case Cons(x,xs) => 
        messages.getOrElse(x, Nil()) == newMessages.getOrElse(x, Nil()) &&
        addUniqueWriteUnserOneBis(x, pair, messages.getOrElse(x, Nil()), messages, channels, m) &&
        uniqueWriteUserOne(x, newMessages.getOrElse(x, Nil()), newMessages, channels) &&
        addUniqueWriteUnser(xs, messages, m, pair) &&
        uniqueWriteUser(channels, newMessages) &&
        true
    }
  }holds
  
  def addUniqueWriteUnserOne(
    pair: (ActorId, ActorId),
    channelMessages: List[Message],
    messages: MMap[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)], 
    m: Message
  ): Boolean = {
    require(
      uniqueWriteUserOne(pair, channelMessages, messages, channels) &&
      {
        m match {
          case WriteUser(s,i) => false
          case _ => true
        }
      } &&
      true
      )
    val newMessages = messages.updated(pair, messages.getOrElse(pair, Nil()) :+ m)
    channelMessages match {
      case Nil() => 
        uniqueWriteUserOne(pair, channelMessages :+ m, newMessages, channels) &&
        true
      case Cons(WriteUser(s,i),xs) => 
        addChannelsNotContains(m, WriteUser(s,i), pair, channels, messages) &&
        channelNotContains(WriteUser(s,i), pair, channels, newMessages) &&
        addUniqueWriteUnserOne(pair, xs, messages, channels, m) &&
        uniqueWriteUserOne(pair, channelMessages :+ m, newMessages, channels) &&
        true
      case Cons(x,xs) => 
        addUniqueWriteUnserOne(pair, xs, messages, channels, m) &&
        uniqueWriteUserOne(pair, channelMessages :+ m, newMessages, channels) &&
        true
    }
  }holds

  
  def addUniqueWriteUnserOneBis(
    pairChannel: (ActorId, ActorId),
    pairAdd: (ActorId, ActorId),
    channelMessages: List[Message],
    messages: MMap[(ActorId, ActorId), List[Message]],
    channels: List[(ActorId, ActorId)], 
    m: Message
  ): Boolean = {
    require(
      uniqueWriteUserOne(pairChannel, channelMessages, messages, channels) &&
      {
        m match {
          case WriteUser(s,i) => false
          case _ => true
        }
      } &&
      true
      )
    val newMessages = messages.updated(pairAdd, messages.getOrElse(pairAdd, Nil()) :+ m)
    channelMessages match {
      case Nil() => 
        uniqueWriteUserOne(pairChannel, channelMessages, newMessages, channels) &&
        true
      case Cons(WriteUser(s,i),xs) => 
        addChannelsNotContainsBis(m, WriteUser(s,i), pairAdd, pairChannel, channels, messages) &&
        channelNotContains(WriteUser(s,i), pairChannel, channels, newMessages) &&
        addUniqueWriteUnserOneBis(pairChannel, pairAdd, xs, messages, channels, m) &&
        uniqueWriteUserOne(pairChannel, channelMessages, newMessages, channels) &&
        true
      case Cons(x,xs) => 
        addUniqueWriteUnserOneBis(pairChannel, pairAdd, xs, messages, channels, m) &&
        uniqueWriteUserOne(pairChannel, channelMessages, newMessages, channels) &&
        true
    }
  }holds
  
  
  def addChannelsNotContainsBis(
    addM: Message,
    m: Message,
    pairAdd: (ActorId, ActorId),
    pairChannel: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    require(channelNotContains(m, pairChannel, channels, messages) && addM != m)
    val newMessages = messages.updated(pairAdd, messages.getOrElse(pairAdd, Nil()) :+ addM)
    channels match {
      case Nil() => channelNotContains(m,pairChannel,channels,newMessages)
      case Cons(x,xs) if (x==pairChannel) => 
        addChannelsNotContainsBis(addM,m,pairAdd, pairChannel, xs, messages) &&
        channelNotContains(m,pairChannel,channels,newMessages)
      case Cons(x,xs) =>
        addChannelsNotContainsBis(addM, m, pairAdd, pairChannel, xs, messages) &&
        channelNotContains(m,pairChannel,channels,newMessages)
    }
  }holds
  
  
  
  
  
  
  def addChannelsNotContains(
    addM: Message,
    m: Message,
    pair: (ActorId, ActorId),
    channels: List[(ActorId, ActorId)],
    messages: MMap[(ActorId, ActorId), List[Message]]
  ): Boolean = {
    require(channelNotContains(m, pair, channels, messages))
    val newMessages = messages.updated(pair, messages.getOrElse(pair, Nil()) :+ addM)
    channels match {
      case Nil() => channelNotContains(m,pair,channels,newMessages)
      case Cons(x,xs) if (x==pair) => 
        addChannelsNotContains(addM,m,pair,xs,messages) &&
        channelNotContains(m,pair,channels,newMessages)
      case Cons(x,xs) =>
        messages.getOrElse(x,Nil()) == newMessages.getOrElse(x,Nil()) &&
        addChannelsNotContains(addM,m,pair,xs,messages) &&
        channelNotContains(m,pair,channels,newMessages)
    }
  }holds
  
}

