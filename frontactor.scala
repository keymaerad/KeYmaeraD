package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._


import Nodes._


class FrontActor extends Actor {

  

  var hereNode: NodeID = 0


  def act(): Unit = {
    println("acting")

    loop (
      react {
        case 'here =>
          displayThisNode
          sender ! ()
        case ('load, filename:String) =>
          loadfile(filename)
          sender ! ()
        case msg =>
          println("got message: " + msg)
          sender ! ()
      }
    )
    
  }


  def displayThisNode : Unit = {
    nodeTable.get(hereNode) match {
      case Some(nd) =>
        println (nd)
        println("nodeID = " + nd.nodeID)
        println("status = " + nd.status)
        println("children = " + nd.children)
      case None =>
        println ("node " + hereNode + " does not exist.")
    }

  }


  def loadfile(filename: String) : Unit = {
    val fi = 
      new java.io.FileInputStream(filename)

    val dlp = new DLParser(fi)

    dlp.result match {
      case Some(g) =>
        val nd = newNode(OrNode,g)
        hereNode = nd.nodeID
      case None =>
        println("failed to load file")

    }

    ()

  }



}

