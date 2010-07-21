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
      case None =>
        println ("node " + hereNode + " does not exist.")
    }

  }


  def loadfile(filename: String) : Unit = {
    val inp = 
     io.Source.fromFile(filename).getLines.reduceLeft(_+_);
    
    val g = 
      Parser.sequent_parser(inp); 

    val nd = newNode(OrNode,g)
    


    ()

  }



}

