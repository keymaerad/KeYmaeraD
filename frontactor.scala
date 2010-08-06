package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._


import Nodes._


object TreeActions {
  

  import RulesUtil._

  def applyrule(hn: OrNode, 
                p: Position, 
                rl: ProofRule): Boolean = rl(p)(hn.goal) match {
    case Some((Nil, _)) => //proved
      val pnd = new DoneNode(rl.toString, hn.goal)
      pnd.parent = Some(hn.nodeID)
      register(pnd)
      hn.children = pnd.nodeID :: hn.children
      propagateProvedUp(hn.nodeID, pnd.nodeID)
      true
    case Some((List(sq), _)) => 
      val ornd = new OrNode(rl.toString, sq)
      ornd.parent = Some(hn.nodeID)
      register(ornd)
      hn.children = ornd.nodeID :: hn.children
      true
    case Some( (sqs, fvs)  ) =>
      val andnd = new AndNode(rl.toString, hn.goal, Nil)
      andnd.parent = Some(hn.nodeID)
      register(andnd)
      val subname = rl.toString + " subgoal"
      val ornds = sqs.map(s => new OrNode(subname, s))
      ornds.map(register _)
      ornds.map(x => x.parent = Some(andnd.nodeID))
      val orndIDs = ornds.map( _.nodeID)
      hn.children = andnd.nodeID :: hn.children 
      andnd.children = orndIDs
      true
    case None => 
      false
  }
    

/* crawl the tree to update statuses.
 * propagateProvedUp is called on nd when a child of nd is proved.
 */
  def propagateProvedUp(ndID: NodeID, from: NodeID): Unit = {
    val nd = getnode(ndID)
    nd match {
      case AndNode(r,g,svs) =>
        val others = nd.children.filterNot( _ ==  from)
        val os = others.map(getnode).map(_.status)
        os.find( _ != Proved) match {
           case None =>
             nd.status = Proved
             nd.parent match {
               case Some(p) =>
                 propagateProvedUp(p, ndID)
               case None =>
             }    
           case Some(_) =>
        }

      case OrNode(r,g) =>
        nd.status = Proved
        val others = nd.children.filterNot( _ ==  from)
        others.map(x => propagateIrrelevantDown(x))
        nd.parent match {
          case Some(p) =>
            propagateProvedUp(p, ndID)
          case None =>
            
        }
      case DoneNode(r,g) =>
        // shouldn't ever happen
        throw new Error("bad call of propagateProvedUp")
    }
  }

  // called when ndID becomes irrelevant.
  def propagateIrrelevantDown(ndID: NodeID) : Unit = {
    val nd = getnode(ndID)
    nd.status = Irrelevant(nd.status)
    nd.children.map( propagateIrrelevantDown)

  }


}



class FrontActor extends Actor {

  import TreeActions._  
  import RulesUtil._

  import Tactics._

  var hereNode: ProofNode = nullNode

  val jobmaster = new Jobs.JobMaster()
  jobmaster.start()

/*
  val rules = new scala.collection.mutable.HashMap[String,ProofRule]()
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
                 */


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
/*        case ('apply, pos: Position, rule: String) =>
          (hereNode, rules.get(rule))  match {
            case (_,None) =>
              println("rule not found")
            case (ornd@OrNode(_,_), Some(rl)) =>
              applyrule(ornd,pos,rl)
            case _ => 
              println("cannot apply rule here")
          }
          sender ! ()
*/
        case ('rule, pos: Position, rl: ProofRule) =>
          hereNode  match {
            case ornd@OrNode(_,_) =>
              val r = applyrule(ornd,pos,rl)
              if(r) println("success")
              else println("rule cannot be applied there")    

            case _ => 
              println("cannot apply rule here")
          }
          sender ! ()

        case ('tactic, tct: Tactic) =>

          hereNode  match {
            case ornd@OrNode(_,_) =>
              tct(ornd)
            case _ => 
              println("cannot apply rule here")
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
              val nd1 = DoneNode("quantifier elimination", sq)
              nd1.parent = Some(nd.nodeID)
              register(nd1)
              nd.addchild(nd1.nodeID)
              propagateProvedUp(ndID, nd1.nodeID)
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
        shownode(ndID)
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
}



