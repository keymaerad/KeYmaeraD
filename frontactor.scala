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
        case msg =>
          println("got message: " + msg)
          sender ! ()
      }
    )
    
  }


  def displayThisNode : Unit = {
    shownode(hereNode)
  }

  def shownode(ndID: NodeID) : Unit = 
    nodeTable.get(ndID) match {
      case Some(nd@ProofNode(typ, gl)) =>
        Printing.printSequent(gl)
        println()
        println("nodeID = " + nd.nodeID)
        println("status = " + nd.status)
        println("children = " + nd.children)
      case None =>
        println ("node " + hereNode + " does not exist.")
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

