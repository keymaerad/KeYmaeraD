package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._

import Procedures._

object Jobs {
  type JobID = Int

  private var nextID = 0

  def nextJobID : JobID = {
    val res = nextID;
    nextID += 1;
    res
  }



  val procs = new scala.collection.mutable.HashMap[String,Procedure]()
  procs ++= List(("ch", CohenHormander))




  case class JobData( s: scala.actors.OutputChannel[Any],
                      t: Long)


  class JobServer extends Actor {

    val jobs = new scala.collection.mutable.HashMap[JobID,JobData ]()



    def act(): Unit = {
      println("jobserver acting")

      loop (
        react {
          case 'quit =>
            sender ! ()
            exit
          case ('job, p: String, sq: Sequent) =>
            procs.get(p) match {
              case Some(pr) =>
                val jid = nextJobID
                val t = System.currentTimeMillis
                val jd = JobData(sender, t)
                jobs.put(jid, jd)
              case None =>
            }
            sender ! ()

         case 'list =>
           println(jobs)
           sender ! ()
          
         case ('abort, jid: JobID) =>
              
        }
      )
    }
  }

}
