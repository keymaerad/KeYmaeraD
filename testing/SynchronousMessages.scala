// Example to show the semantics of synchronous messages.
// The output of this program is, after a 2.5 second pause:
//  r = 6
// got message: 1
// got message: 2
// got message: 3
// got message: 4
// got message: 5

package Testing

import scala.actors.Actor
import scala.actors.TIMEOUT
import scala.actors.AbstractActor
import scala.actors.Actor._
import scala.actors.Futures._

class Server extends Actor {

  var counter: Int = 0

  def act() :Unit = {
    while (true) {
      receive {
        case 'a =>
          Thread.sleep(500)
          counter += 1
          reply(counter)
        case 'r => 
          counter += 1
          reply(counter)
      }
    }
  }
}

class Client extends Actor {
  def act() : Unit = {
    val server = new Server
    server.start
    
    for (i <- List(1,2,3,4,5)) {
       server ! 'a
    }

    val r = server !? 'r

    println(" r = " + r);
    while (true) {
      receive {
        case msg => 
          println("got message: " + msg)
      }
    }    
  }
}

object Main {
  def main(args: Array[String]) : Unit = {
    val client = new Client
    client.start
  }

}
