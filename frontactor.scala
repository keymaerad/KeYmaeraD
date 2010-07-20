package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._


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

