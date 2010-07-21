package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._



trait TreeNode {
  val goal : Goal
  val children : List[TreeNode]
  var status : Status

}


object Nodes {

  type NodeID = Int

  val nodeTable = new scala.collection.mutable.HashMap[NodeID, TreeNode]

  var nextID = 0

  

}



class FrontActor extends Actor {

  def act(): Unit = {
    println("acting")

    loop (
      react {
        case msg =>
          println("got message: " + msg)
      }
    )
    
  }



}

