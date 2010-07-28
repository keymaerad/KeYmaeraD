package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._


import Nodes._


class FrontActor extends Actor {

  

  var hereNode: ProofNode = nullNode


  val rules = new scala.collection.mutable.HashMap[String,Rules.ProofRule]()
  rules ++= List(("andLeft", Rules.andLeft),
                 ("andRight", Rules.andRight),
                 ("orRight", Rules.orRight),
                 ("orLeft", Rules.orLeft),
                 ("seq", Rules.seq),
                 ("chooseRight", Rules.chooseRight),
                 ("checkRight", Rules.checkRight),
                 ("assignRight", Rules.assignRight),
                 ("assignAnyRight", Rules.assignAnyRight))


  def act(): Unit = {
    println("acting")

    loop (
      react {
        case 'quit =>
          sender ! ()
          exit
        case 'here =>
          displayThisNode
          sender ! ()
        case ('load, filename:String) =>
          loadfile(filename)
          sender ! ()
        case ('show, nd: NodeID) =>
          shownode(nd)
          sender ! ()
        case ('goto, nd: NodeID) =>
          gotonode(nd)
          sender ! ()
        case ('apply, pos: Rules.Position, rule: String) =>
          applyrule(pos,rule)
          sender ! ()
        case msg =>
          println("got message: " + msg)
          sender ! ()
      }
    )
    
  }


  def displayThisNode : Unit = {
    shownode(hereNode.nodeID)
  }

  def shownode(ndID: NodeID) : Unit = 
    nodeTable.get(ndID) match {
      case Some(nd) =>
        println(nd.toString)
      case None =>
        println ("node " + ndID + " does not exist.")
    }


  def gotonode(ndID: NodeID) : Unit = 
    nodeTable.get(ndID) match {
      case Some(nd) =>
        hereNode = nd
        println("now at node " + ndID )
      case None =>
        println ("node " + ndID + " does not exist.")
    }



  def loadfile(filename: String) : Unit = {
    val fi = 
      new java.io.FileInputStream(filename)

    val dlp = new DLParser(fi)

    dlp.result match {
      case Some(g) =>
        val nd = new OrNode("loaded from " + filename, g)
        register(nd)
        hereNode = nd
      case None =>
        println("failed to load file")

    }

    ()

  }

  def applyrule(p: Rules.Position, r: String): Unit = rules.get(r) match {
    case Some(rl) =>
          rl(p)(hereNode.goal) match {
            case Some( (sqs, fvs)  ) =>
              val andnd = new AndNode(r, hereNode.goal, Nil)
              register(andnd)
              val subname = r + " subgoal"
              val ornds = sqs.map(s => new OrNode(subname, s))
              ornds.map(register _)
              val orndIDs = ornds.map( _.nodeID)
              hereNode.children = andnd.nodeID :: hereNode.children 
              andnd.children = orndIDs
              println("success")
            case None => 
              println("rule cannot be applied there")    
          }
    case None =>
      println("rule " + r + " not found.")
  }
    






}

