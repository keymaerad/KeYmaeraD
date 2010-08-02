package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._
import scala.actors.Futures._

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
                      t: Long,
                      w: scala.actors.AbstractActor)


  class JobServer extends Actor {

    val jobs = new scala.collection.mutable.HashMap[JobID,JobData ]()

    val localworker = new JobWorker()


    def act(): Unit = {
      println("jobserver acting")

      loop (
        react {
          case 'quit =>
            sender ! ()
            exit
          case ('job, p: String, sq: Sequent) =>
            val jid = nextJobID
            val t = System.currentTimeMillis
            jobs.put(jid, JobData(sender, t, localworker))
            localworker !? ( ('job, p, sq, jid) )
            sender ! ()

         case 'list =>
           println(jobs)
           sender ! ()
          

         case ('jobdone, jid: JobID, res: Sequent) =>

         case ('jobdone, jid: JobID) =>

         case ('abort, jid: JobID) =>
              
        }
      )
    }
  }






  class JobWorker extends Actor {


    var jobsender: scala.actors.OutputChannel[Any] = self
    var proc: Option[Procedure] = None

    def act(): Unit = {
      println("jobworker acting")

      loop (
        react {
          case 'quit =>
            sender ! ()
            exit
          case ('job, p: String, sq: Sequent, jid: JobID) =>
            jobsender = sender
            procs.get(p) match {
              case Some(pr) =>
                val sf = self
                proc = Some(pr)
                future ({
                  val res = pr.proceed(sq)
                  proc = None
                  res match {
                    case Some(r) =>
                      sf ! ('done, jid, r)
                    case None =>
                      sf ! ('done, jid)
                  }

                })

              case None =>
                
            }
            sender ! ()


         case ('done, jid:JobID, res: Sequent) =>
           jobsender ! ('jobdone, jid, res)
          
         case ('done, jid: JobID) =>
           jobsender ! ('jobdone, jid)
         
         case 'abort => 
           proc match {
             case Some(pr) =>
               pr.abort
             case None => 
               println("got abort when nothing was running")
           }
           sender ! ()
              
        }
      )
    }
  }




}
