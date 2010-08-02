package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._


import Nodes._


class FrontActor extends Actor {

  

  var hereNode: ProofNode = nullNode

  val jobmaster = new Jobs.JobMaster()
  jobmaster.start()


  val rules = new scala.collection.mutable.HashMap[String,Rules.ProofRule]()
  rules ++= List(("close", Rules.close),
                 ("andLeft", Rules.andLeft),
                 ("andRight", Rules.andRight),
                 ("orRight", Rules.orRight),
                 ("orLeft", Rules.orLeft),
                 ("seq", Rules.seq),
                 ("chooseRight", Rules.chooseRight),
                 ("checkRight", Rules.checkRight),
                 ("assignRight", Rules.assignRight),
                 ("assignAnyRight", Rules.assignAnyRight))


  val jobs = new scala.collection.mutable.HashMap[NodeID, Long]()

  def act(): Unit = {
    println("acting")

    loop (
      react {
        case 'quit =>
          println("frontactor quitting")
          jobmaster !? 'quit
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
        case ('goto, nd: NodeID) =>
          gotonode(nd)
          sender ! ()
        case ('apply, pos: Rules.Position, rule: String) =>
          hereNode match {
            case AndNode(_,_,_) =>
              println("cannot apply rule to an AndNode")
            case ornd@OrNode(_,_) =>
              applyrule(ornd,pos,rule)
          }
          sender ! ()
        case ('job, proc: String) => 
          (Procedures.procs.get(proc), hereNode) match {
            case (_,AndNode(_,_,_)) =>
              println("cannot do a procedure on an AndNode")
            case (None, _ ) =>
              println("not a defined procedure: " + proc)
            case (Some(pr), ornd@OrNode(r,sq)) =>
              if(pr.applies(sq)) {
                jobmaster ! (('job, proc, sq, ornd.nodeID))
                val t = System.currentTimeMillis
                jobs.put(ornd.nodeID, t)
              } else {
                println("procedure " + proc + " does not apply here.")
              }
              
          }
          sender ! ()

        case ('jobdone, ndID: NodeID, sq: Sequent) =>
          jobs.remove(ndID)
          nodeTable.get(ndID) match {
            case Some(nd) => 
              val nd1 = BackendNode("quantifier elimination", sq)
              register(nd1)
              nd.addchild(nd1.nodeID)
            case None => 
              throw new Error("node not in nodeTable")
          }


        case ('jobdone, ndID: NodeID) =>
          jobs.remove(ndID)


        case 'jobs =>
          println(jobs.toList)
          sender ! ()

        case msg =>
          println("got message: " + msg)
          sender ! ()
      }
    )
    
  }


  def displayThisNode : Unit = {
    shownode(hereNode.nodeID)
  }

  def shownode(ndID: NodeID) : Unit = 
    nodeTable.get(ndID) match {
      case Some(nd) =>
        println(nd.toString)
      case None =>
        println ("node " + ndID + " does not exist.")
    }


  def gotonode(ndID: NodeID) : Unit = 
    nodeTable.get(ndID) match {
      case Some(nd) =>
        hereNode = nd
        println("now at node " + ndID )
      case None =>
        println ("node " + ndID + " does not exist.")
    }



  def loadfile(filename: String) : Unit = {
    val fi = 
      new java.io.FileInputStream(filename)

    val dlp = new DLParser(fi)

    dlp.result match {
      case Some(g) =>
        val nd = new OrNode("loaded from " + filename, g)
        register(nd)
        hereNode = nd
      case None =>
        println("failed to load file")

    }

    ()

  }

  

  def applyrule(hn: OrNode, 
                p: Rules.Position, r: String): Unit = rules.get(r) match {
    case Some(rl) =>
          rl(p)(hn.goal) match {
            case Some( (sqs, fvs)  ) =>
              val andnd = new AndNode(r, hn.goal, Nil)
              register(andnd)
              val subname = r + " subgoal"
              val ornds = sqs.map(s => new OrNode(subname, s))
              ornds.map(register _)
              val orndIDs = ornds.map( _.nodeID)
              hn.children = andnd.nodeID :: hn.children 
              andnd.children = orndIDs
              println("success")
            case None => 
              println("rule cannot be applied there")    
          }
    case None =>
      println("rule " + r + " not found.")
  }
    

}

