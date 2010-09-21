package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._
import scala.actors.Futures._

import scala.actors.remote.RemoteActor
import scala.actors.remote.RemoteActor._
import scala.actors.remote._


import Procedures._

object Jobs {
  type JobID = Nodes.NodeID

/*
  private var nextID = 0

  def nextJobID : JobID = {
    val res = nextID;
    nextID += 1;
    res
  }
*/






  case class JobData( s: scala.actors.OutputChannel[Any],
                      t: Long,
                      w: scala.actors.AbstractActor)


  class JobMaster extends Actor {

    val jobs = new scala.collection.mutable.HashMap[JobID,JobData ]()

    val localworker = new JobWorker()
    localworker.start()
  

    def act(): Unit = {
      println("jobmaster acting")

      loop (
        react {
          case 'quit =>
            println("jobmaster quitting")
            localworker !? 'quit
            sender ! ()
            exit

          // worker registration.
          case ('register, Node(ip,prt)) =>
            ()
            


          case ('job, p: String, sq: Sequent, jid: JobID) =>
//            val jid = nextJobID
            val t = System.currentTimeMillis
            // TODO: easy filter.
            jobs.put(jid, JobData(sender, t, localworker))
            localworker ! ( ('job, p, sq, jid) )

         case 'list =>
           println(jobs)
          

         case ('jobdone, jid: JobID, res: Sequent) =>
           jobs.get(jid) match {
             case Some(JobData(s,t,w)) =>
               s ! ('jobdone, jid,res)
             case None =>
               throw new Error("invalid jobID")
           }
           jobs.remove(jid)

         case ('jobdone, jid: JobID) =>
           jobs.get(jid) match {
             case Some(JobData(s,t,w)) =>
               s ! ('jobdone, jid)
             case None =>
               throw new Error("invalid jobID")
           }
           jobs.remove(jid)

         case ('abort, jid: JobID) =>
           jobs.get(jid) match {
             case Some(JobData(s,t,w)) =>
               w ! 'abort
             case None =>
               
           }

          
          case msg =>
            println ("jobserver got message: " + msg)

        }
      )
    }
  }





  class JobWorker extends Actor {

    case class JobData(proc:String, 
                       sq:Sequent,
                       jid: JobID,
                       sender:scala.actors.OutputChannel[Any])

    var working: Option[Procedure]  = None

    val procqueue = 
      new scala.collection.mutable.Queue[JobData]()


    def tryworking : Unit = {
      if (working == None  && ! procqueue.isEmpty) {
        val jd@JobData(p,sq,jid,sender) = procqueue.dequeue
        procs.get(p) match {
          case Some(pr) =>
            val sf = self
            if(pr.applies(sq)) {
              working = Some(pr)
              future ({
                val res = pr.proceed(sq)
                res match {
                  case Some(r) =>
                    sf ! ('done, jd, r)
                  case None =>
                    sf ! ('done, jd)
                }
              })
            }  else  sf ! ('doesnotapply, jid) // should not happen
                

          case None =>
            // should not happen
        }
      }
    }



    def act(): Unit = {
      println("jobworker acting")

      while(true){
        tryworking
        receive {
          case 'quit =>
            sender ! ()
            exit
          case ('job, p: String, sq: Sequent, jid: JobID) =>
           procqueue.enqueue(JobData(p,sq,jid, sender))

         case ('done, JobData(p,sq,jid,jobsender), res: Sequent) =>
           working = None
           jobsender ! ('jobdone, jid, res)
          
         case ('done, JobData(p,sq,jid,jobsender)) =>
           working = None
           jobsender ! ('jobdone, jid)
         
         case 'abort => 
           working match {
             case Some(pr) =>
               pr.abort
             case None => // XXX need to look through the queue
               println("got abort when nothing was running")
           }
              
        }
      }
    }
  }









  private object Worker {
  
    import org.apache.commons.cli.Options
    import org.apache.commons.cli.CommandLine
    import java.net.InetAddress


    def parse(args: Array[String]) : CommandLine = {

      //use CLI to parse command line options
      var opts = new org.apache.commons.cli.Options();
      opts.addOption("c", true, "coordinator address");
      opts.addOption("cp", true, "coordinator port (default = 9500)");
      opts.addOption("p", true, "port this worker should run on");

      //do parsing
      var parser = new org.apache.commons.cli.GnuParser();
      parser.parse( opts, args);

    }

    def main(args: Array[String]) : Unit = {
      println("worker says: hello world.")

      val cmd = parse(args)
      
      //process options
      //coordinator address and port
      if (!cmd.hasOption("c")) {
        println("Forgot to supply coordinator address. (use -c). Quitting.")
        System.exit(0);
      }

      val coorHost = 
        new Node(cmd.getOptionValue("c"), 
                 java.lang.Integer.parseInt(cmd.getOptionValue("cp", "9500")))
      
      println("coordinator at " + coorHost.toString)
      
      //get thisHost
      //TBD: put in cheesy option bind workaround ... default to 9001 for now
      val thisAddr = InetAddress.getLocalHost().getHostAddress()
      val thisHost = 
        Node(thisAddr, 
             java.lang.Integer.parseInt(cmd.getOptionValue("p", "9001")))


      
      //val listenerActor = new ListenerActor(coorHost, thisHost)
      //listenerActor.start
      ()
    }

  }



}
