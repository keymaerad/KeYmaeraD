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


  class SyncMap[A,B] 
    extends scala.collection.mutable.HashMap[A, B]
    with scala.collection.mutable.SynchronizedMap[A,B]
    

  case class JobData( jid: JobID,
                      s: scala.actors.OutputChannel[Any],
                      p: String, // the proc
                      sq: Sequent, 
                      t: Long // start time
                   )

  class JobMaster(myPort: Int) extends Actor {

    // the jobs we've sent out to workers
    val jobs = new scala.collection.mutable.HashMap[JobID, (JobData, Node)]()


    /* Keep a queue of unstarted jobs and idling workers.
     * At each loop, match them up and dispatch.
     */

    val newjobs = new scala.collection.mutable.Queue[JobData]()
    val idleworkers = new scala.collection.mutable.Queue[Node]()
    val allworkers = new scala.collection.mutable.LinkedList[scala.actors.OutputChannel[Any]]()

//    val localworker = new JobWorker()
//    localworker.start()
  

    def act(): Unit = {
      println("jobmaster acting")

      RemoteActor.classLoader = getClass().getClassLoader()

      alive(myPort)
      register('master, self)


      while(true){

        // Assign jobs if we can.
        while((! idleworkers.isEmpty) && (! newjobs.isEmpty) ){
          val iw = idleworkers.dequeue()
          val jd@JobData(jid, s,p,sq,t) = newjobs.dequeue()
          val actr = select(iw, 'worker)
          actr ! ( ('job, p, sq, jid) )
          jobs.put(jid,(jd, iw))
          ()
        };

//        println("jobmaster listening")
        receive {
          case 'quit =>
            println("jobmaster quitting, notifying workers")
//            localworker !? 'quit
            for(w <- allworkers){
                w ! ('quitting)
            }
            println("jobmaster quits")
            sender ! ()
            exit

          // worker registration.
          case ('register, nd@Node(ip,prt)) =>
            println("got a registration.") 
            //@TODO following line doesn't have much effect, what do we need to remember in allworkers so that we can talk to this worker later?
            allworkers :+ sender
            sender ! ('registered)
            ()
            

          case ('idling, nd@Node(ip,prt)) =>
            idleworkers.enqueue( nd)
            ()

          case ('job, p: String, sq: Sequent, jid: JobID) =>
//            val jid = nextJobID
            val t = System.currentTimeMillis
            // PERF: insert easy filter here.
            newjobs += JobData(jid, sender, p, sq, t)

         case 'list =>
           println(jobs)
          

         case ('jobdone, jid: JobID, res: Sequent) =>
           jobs.get(jid) match {
             case Some((JobData(_,s,p,sq,t),w)) =>
               s ! ('jobdone, jid,res)
             case None =>
               throw new Error("invalid jobID")
           }
           jobs.remove(jid)

         case ('jobdone, jid: JobID) =>
           jobs.get(jid) match {
             case Some((JobData(_,s,p,sq,t),w)) =>
               s ! ('jobdone, jid)
             case None =>
               throw new Error("invalid jobID")
           }
           jobs.remove(jid)

         case ('abort, jid: JobID) =>
          val njs = newjobs.dequeueAll( {case JobData(x,_,_,_,_) => x == jid})
          println("jobmaster: cancelling "+ njs.length +   " job(s) ")
          for(JobData(jid1,s,p,sq,t) <- njs){
            s ! ('jobdone,jid1) 
          }
          jobs.get(jid) match {
            case Some((JobData(_,s,p,sq,t), nd)) =>
              println("jobmaster: aborting job " + jid)
              val actr = select(nd,'worker)
              actr ! 'abort
            case None =>
              if (njs.length == 0)
                println("jobmaster: could not find job " + jid)
            
          }


          
          case msg =>
            println ("jobserver got message: " + msg)

        }
      }
    }
  }





  class JobWorker(masterNode: Node, myNode: Node) extends Actor {

    case class JobData(proc:String, 
                       sq:Sequent,
                       jid: JobID,
                       sender:scala.actors.OutputChannel[Any])

    var working: Option[Procedure]  = None

    val procqueue = 
      new scala.collection.mutable.Queue[JobData]()

    val master = select(masterNode, 'master)

    val lock = new Object()

    def doRegistration(coorHost: Node, thisHost: Node) = {

      alive(thisHost.port)
      register('worker, self)


      println("this host: " + thisHost.toString)
      master ! ('register, thisHost)
    
      println("waiting for ack from master")
      receive {
        case ('registered) =>
          println("got ack.")
          ()
        case msg => 
          throw new Error("not an ack: " + msg)
      }

      ()
  }


    def tryworking : Unit = {
      if (working == None  && ! procqueue.isEmpty) {
        println("procqueue has length " + procqueue.length)
        val jd@JobData(p,sq,jid,sender) = procqueue.dequeue
        procs.get(p) match {
          case Some(pr) =>
            val sf = self
            if(pr.applies(sq)) {
              println("working on jid " + jid)
              lock.synchronized{
                working = Some(pr)
              }
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
    
    private def abort() = {
        lock.synchronized{ working } match {
          case Some(pr) =>
            pr.abort
          case None => // XXX need to look through the queue
            println("got abort when nothing was running")
        }
    }


    def act(): Unit = {
      println("jobworker acting")

      println("registering...")

      doRegistration(masterNode, myNode)
      
      println("registered.")

      master ! ('idling, myNode)

      while(true){
        tryworking
        receive {
          case 'quit =>
            sender ! ()
            exit

          case 'quitting =>
            println("jobmaster quitting, worker exits")
            abort()
            println("jobmaster quitting, worker exits")
            sender ! ()
            exit

          case ('job, p: String, sq: Sequent, jid: JobID) =>
           procqueue.enqueue(JobData(p,sq,jid, sender))

         case ('done, JobData(p,sq,jid,jobsender), res: Sequent) =>
           lock.synchronized {working = None}
           jobsender ! ('jobdone, jid, res)
          master ! ('idling, myNode)
          
         case ('done, JobData(p,sq,jid,jobsender)) =>
           lock.synchronized  { working = None }
           jobsender ! ('jobdone, jid)
           master ! ('idling, myNode)
         
         case 'abort => 
           abort()
        }
      }
    }
  }


}



// Code entry point for workers.
 object WorkerMain {
   import Jobs._
  
    import org.apache.commons.cli.Options
    import org.apache.commons.cli.CommandLine
    import java.net.InetAddress


    def parse(args: Array[String]) : CommandLine = {

      //use CLI to parse command line options
      var opts = new org.apache.commons.cli.Options();
      opts.addOption("c", true, "coordinator address (default = localhost)");
      opts.addOption("cp", true, "coordinator port (default = 50001)");
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
        println("Using default coordinator address localhost. (use -c to specify).")
      }

      val coorHost = 
        new Node(cmd.getOptionValue("c","localhost"), 
                 java.lang.Integer.parseInt(cmd.getOptionValue("cp", "50001")))
      
      println("coordinator at " + coorHost.toString)
      
      val thisAddr = InetAddress.getLocalHost().getHostAddress()
      var thisPort = java.lang.Integer.parseInt(cmd.getOptionValue("p", "0"))
      if (thisPort == 0)
	      try {
		  	  // port=0 supposedly says automatically allocate ephemeral port @see ServerSocket
		      val testSocket = new java.net.ServerSocket(0)
		      thisPort = testSocket.getLocalPort()
		      testSocket.close()
          }
          catch {
	          case ioe: java.io.IOException =>
	              thisPort = 50002 + scala.util.Random.nextInt(10000)
          }
      val thisHost = Node(thisAddr, thisPort)


      
      val jobWorker = new JobWorker(coorHost, thisHost)
      jobWorker.start
      ()
    }

  }

