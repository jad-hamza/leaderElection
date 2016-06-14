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
 
 
  def makeInitMem(l: List[Variable]): List[(Variable,BigInt)] = {
    require(!l.isEmpty)
    l match {
      case Cons(x,Nil()) => List((x,0))
      case Cons(x,xs) => Cons((x,0),makeInitMem(xs))
    }
  }
  
  val init_mem = makeInitMem(correct_variables)
  
   val init_param = Variables(correct_variables)
  
  
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

  val init_states_list = List[(ActorId, State)](
    (a1,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
    (a2,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
    (a3,CommonState(MMap.makeMap[Variable,BigInt](init_mem), Set())),
    (a4,UserState(Nil(),0))
    )
  val init_states = MMap.makeMap[ActorId,State](init_states_list)

  
  val init_getActor_list = List[(ActorId,Actor)](
    (a1,SystemActor(a1)),
    (a2,SystemActor(a2)),
    (a3,SystemActor(a3)),
    (a4,UserActor(a4))
    )
  val init_getActor = MMap.makeMap[ActorId,Actor](init_getActor_list)
    
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
    checkContent(init_states_list, init_states) && 
    checkContent(init_getActor_list, init_getActor) &&
    res.getActor(a1) == SystemActor(a1) &&
    res.getActor(a2) == SystemActor(a2) &&
    res.getActor(a3) == SystemActor(a3) &&
    res.getActor(a4) == UserActor(a4) && 
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
    getActor(a1) == SystemActor(a1) &&
    getActor(a2) == SystemActor(a2) &&
    getActor(a3) == SystemActor(a3) &&
    getActor(a4) == UserActor(a4) && 
    WriteHistory(messages, states)  &&
    tableHistory(param, states) &&
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
  
  def systemActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    (receiver.myId == a1 || receiver.myId == a2 || receiver.myId == a3) &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) && 
    {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }} && {
    val UserState(userHistory,c) = net.states(a4)

    val myId = receiver.myId

    (sender, m, receiver.state) match {
      case (id, WriteUser(s,i,idM), CommonState(mem,h)) => 
        if (idM == (true, s, i)) {
          val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
          val Variables(variables) = net.param
          val newMessages = net.messages.updated((myId,a1), net.messages.getOrElse((myId,a1), Nil()) :+ WriteSystem(s,i,idM,h))
          val newMessages2 = newMessages.updated((myId,a2), newMessages.getOrElse((myId,a2),Nil()) :+ WriteSystem(s,i,idM,h))
          val newMessages3 = newMessages2.updated((myId,a3), newMessages2.getOrElse((myId,a3), Nil()) :+ WriteSystem(s,i,idM,h))
          val newMessages4 = newMessages3.updated((myId,a4), newMessages3.getOrElse((myId,a4),Nil()) :+ AckUser(idM,h))
          val UserState(newUserHistory,newc) = newStates(a4)
          (userHistory == newUserHistory) &&
          (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteSystem(s,i,idM,h), myId, a1)) &&
          (ajoutCheckWriteForAll(channels, newMessages, userHistory, WriteSystem(s,i,idM,h), myId, a2)) &&
          (ajoutCheckWriteForAll(channels, newMessages2, userHistory, WriteSystem(s,i,idM,h), myId, a3)) &&
          (ajoutCheckWriteForAll(channels, newMessages3, userHistory, AckUser(idM,h), myId, a4)) &&
          WriteHistory(newMessages, net.states)  &&
          newUserHistory.contains((true, s, i), Set()) &&
          networkInvariant(net.param, net.states, newMessages4, net.getActor) &&
          true
        }
        else true

//       case (id, WriteSystem(s,i,idM,hs), CommonState(mem,h)) =>
//         if (id != myId && (idM == (true, s, i))) {
//           if (checkHistory(h,hs)){
//             val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
//             val UserState(newUserHistory,newc) = newStates(a4)
//             (userHistory == newUserHistory) &&
//             networkInvariant(net.param, newStates, net.messages, net.getActor)
//           }
//           else {
//             val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
//             (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
//             networkInvariant(net.param, net.states, newMessages, net.getActor)
//           }
//         }
//         else {
//           true 
//         }
//     
//       case (id,WriteWaiting(s,i,idM,hs), CommonState(mem,h)) => 
//         if (idM == (true, s, i)) {
//           if (checkHistory(h,hs)){
//             val newStates = net.states.updated(myId, CommonState(mem.updated(s,i),h++Set(idM)))
//             val UserState(newUserHistory,newc) = newStates(a4)
//             (userHistory == newUserHistory) &&
//             networkInvariant(net.param, newStates, net.messages, net.getActor)
//           }
//           else {
//             val newMessages = net.messages.updated((myId,myId), net.messages.getOrElse((myId,myId), Nil()) :+ WriteWaiting(s,i,idM,hs))
//             (ajoutCheckWriteForAll(channels, net.messages, userHistory, WriteWaiting(s,i,idM,hs), myId, myId)) &&
//             networkInvariant(net.param, net.states, newMessages, net.getActor)
//           }
//         }
//         else true
// 
//       case (id,Read(s,idM), CommonState(mem,h)) =>
//         if (id == a4 && (idM._1 == false) && (idM._2 == s)) {
//           val newMessages = net.messages.updated((myId,a4), net.messages.getOrElse((myId,a4), Nil()) :+ Value(mem.getOrElse(s,0),(idM._1, idM._2, mem.getOrElse(s,0)),h))
//           ajoutCheckWriteForAll(channels, net.messages, userHistory, Value(mem.getOrElse(s,0), (idM._1, idM._2, mem.getOrElse(s,0)), h), myId, id) &&
//           networkInvariant(net.param, net.states, newMessages, net.getActor)
//         }
//        else true

      case _ => true
      }
    }
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    networkInvariant(net.param, net.states, net.messages, net.getActor) && {
    val UserState(userHistory,c) = net.states(a4)
    m match {
        case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
        case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
        case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
        case _ => true
    }} && (
    a match {
      case UserActor(_) => userActorReceivePre(a, sender, m)
      case SystemActor(_) => systemActorReceivePre(a, sender, m)
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
              inChannels(n, sender,receiver)&&
              inUserHistory(sender, receiver, n.messages, channels, h)&&
              checkWrite(sms, h)
              networkInvariant(n.param, n.states, messages2, n.getActor)
              true
            case _ => networkInvariant(n.param, n.states, messages2, n.getActor)
          }
 
      case _ => 
        true
    }
  } holds

  def initPre(myId: ActorId, net: VerifiedNetwork) = {
    myId == a4 &&
    networkInvariant(net.param, net.states, net.messages, net.getActor) && {
    val UserState(h,c) = net.states(myId)
    val newHistory: List[((Boolean, Variable, BigInt),Set[(Boolean, Variable, BigInt)])] = Cons(((true, Variable(1),1),Set()), h)
    val newStates = net.states.updated(a4,UserState(newHistory,c+1))
    val messages = net.messages.getOrElse((a4,a1), Nil())
    val newMessages = net.messages.updated((a4,a1),messages:+WriteUser(Variable(1),1,(true, Variable(1),1)))
    
    ajoutUserCheckWriteForAll(channels, net.messages, h, ((true, Variable(1),1),Set())) &&
    networkInvariant(net.param, newStates, net.messages, net.getActor) &&
    ajoutCheckWriteForAll(channels, net.messages, newHistory, WriteUser(Variable(1), 1, (true, Variable(1),1)), a4, a1) &&  
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
          case WriteUser(y,v,idM) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case WriteSystem(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case WriteWaiting(y,v,idM,h) => userHistory.contains((idM,Set())) && checkWrite(q, userHistory)
          case _ => checkWrite(q, userHistory)
        }
    }
  }

  def checkWrite2(l: List[Message], userHistory: List[(Boolean, Variable, BigInt)]):Boolean = {
    l match {
      case Nil() => true
      case Cons(x,q) =>
        x match {
          case WriteUser(y,v,idM) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case WriteSystem(y,v,idM,h) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case WriteWaiting(y,v,idM,h) => userHistory.contains(idM) && checkWrite2(q, userHistory)
          case _ => checkWrite2(q, userHistory)
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
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
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
          case WriteUser(x,v,idM) => userHistory.contains((idM,Set()))
          case WriteSystem(x,v,idM,h) => userHistory.contains((idM,Set()))
          case WriteWaiting(x,v,idM,h) => userHistory.contains((idM,Set()))
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
            else true
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
            else true
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
    require{tableHistory(param, states) && {
      val UserState(h,c) = states(a4)
      h.contains((true, x, v), Set())
      }
    }
    tableHistory(param, states) && states.contains(a1) && {
    val UserState(userHistory, c) = states(a4)
    val Variables(variables) = param
    if (id == a1) {
      val CommonState(mem, h) = states(id)
      val newStates = states.updated(id, CommonState(mem.updated(x,v),h++Set((true, x, v))))
      (newStates(a2) == states(a2)) &&
      (newStates(a3) == states(a3)) &&
      (newStates(a4) == states(a4)) &&
      tableHistoryOne(variables, newStates(a2), userHistory) &&
      tableHistoryOne(variables, newStates(a3), userHistory) &&
      userHistory.contains((true, x, v), Set()) &&
      updateCheckTableOne(variables, states(a1), userHistory, x, v) &&
      tableHistoryOne(variables, newStates(a1), userHistory)&&
      //tableHistory(param, newStates)
      true
    }
    else true
  }
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
        state match {
          case CommonState(mem,h) => 
            if (mem.getOrElse(x,0) != 0) {
              if (x==s) {
                mem.updated(s,i).getOrElse(x,0) == i &&
                userHistory.contains((true, x, mem.updated(s,i).getOrElse(x,0)), Set()) &&
                updateCheckTableOne(xs, state, userHistory, s, i) 
              }
              else {
                mem.updated(s,i).getOrElse(x,0) == mem.getOrElse(x,0) &&
                userHistory.contains((true, x, mem.updated(s,i).getOrElse(x,0)), Set()) &&
                updateCheckTableOne(xs, state, userHistory, s, i)
              }
            }
            else true
          case _ => false
        }
    }
  }holds
  
  
}
