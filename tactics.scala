package DLBanyan


object Tactics {

  import Nodes._
  import TreeActions._
  import RulesUtil._
  import Rules._

  
  // A tactic returns a list of the new open leaves that it spawns.

  abstract class Tactic(name: String) extends ((OrNode) =>  List[NodeID]) {
    override def toString: String = {
      name
    }
  }


  def trylistofrules(rs: List[ProofRule], nd: OrNode) 
         : (Boolean,List[NodeID]) = {
        val sq = nd.goal;
        var foundone = false;
        var res: List[NodeID] = Nil;
   
        for (p <- positions(sq)) {
            for(r <- rs) {
              if(foundone == false){
            
                val res0 = r.apply(p)(sq);
                res0 match {
                  case Some(_) =>
                    res = applyrule(nd,p,r) match { case Some(lst) => lst
                                                     case None => Nil};
                    foundone = true;
                    ()
                  case None => 
                    ()
                }
              }
            }
          }
      (foundone, res)
  }

  val trylistofrulesT : List[ProofRule] => Tactic = rls =>
    new Tactic("trylist " + rls) {
      def apply(nd: OrNode) : List[NodeID] = {
        trylistofrules(rls, nd)._2
      }
    }

  val tryruleatT : ProofRule => Position => Tactic = rl => pos =>
    new Tactic("trylist " + rl +  " " + pos ) {
      def apply(nd: OrNode) : List[NodeID] = {
        val res0 = rl.apply(pos)(nd.goal)
        res0 match {
          case Some(_) =>
            applyrule(nd,pos,rl) match { case Some(lst) => lst
                                     case None => Nil};
          case None =>
            Nil
        }
      }
    }


  def usehints(pos: Position): Tactic = new Tactic("usehints") {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Modality(Box,Loop(hp, True, inv_hints), phi) => 
        val rules = inv_hints.map(loopInduction)
        rules.map(r => applyrule(nd, pos, r)).flatten.flatten
      case Modality(Box,Evolve(derivs,h,inv_hints,sols), phi) =>
        val inv_rules = inv_hints.map(diffStrengthen)
        val inv_res = inv_rules.map(r => applyrule(nd, pos, r)).flatten.flatten
        val sol_rule1 = diffSolve(Endpoint)(sols)
        val sol_rule2 = diffSolve(Standard)(sols)
        val sol_res1 = applyrule(nd,pos,sol_rule1) match {
          case None => Nil
          case Some(lst) => lst
        }
        val sol_res2 = applyrule(nd,pos,sol_rule2) match {
          case None => Nil
          case Some(lst) => lst
        } 
        sol_res1 ++ sol_res2 ++ inv_res

        
      case _ => Nil
    }
  }


  val hpeasy = List(seq, choose, check, 
                    assign, assignAnyRight, qassign,
                    diffClose
                  )

  val needhints = List(loopInduction, diffStrengthen)


  def composeT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("compose " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) = {
        val newnds = t1(nd)
        newnds.map(c => 
          {getnodethen(c,gotonode _);
           hereNode match {
                case ornd@OrNode(_,_) =>
                  t2(ornd)
                case _ => Nil
              }}).flatten 
      }

    }


  // do t1. Then, if no new nodes, do t2.
  def eitherT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("either " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) = {
        val nds = t1.apply(nd);
        nds match {
          case Nil => 
            t2.apply(nd)
          case rs => 
            nds
        }
        
      }
    }



  val hpeasyT : Tactic = new Tactic("hpeasy") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(c,List(s)) =>
        // try all the box hp easy rules
        val pos = RightP(0)
        val (_,nds1) = trylistofrules(hpeasy, nd)
        val nds2 = usehints(pos)(nd)
        nds1 ++ nds2
      case _ => Nil
    }
  }


  def repeatT(t: Tactic) : Tactic = new Tactic("repeat " + t.toString) {
    def apply(nd: OrNode) = {
      val newnds = t(nd)
      if (newnds.length == 0) List(nd.nodeID)
      else newnds.map( 
        c => {getnodethen(c,gotonode _);
              hereNode match {
                case ornd@OrNode(_,_) =>
                  apply(ornd)
                case _ => Nil
              }
            }).flatten

    }

  }



  val substT : Tactic = new Tactic("substitute") {
    def apply(nd: OrNode) = nd.goal match {
      case sq@Sequent(c,s) =>

        var foundone = false;
        var res: List[NodeID] = Nil;
      
        for (i <- c.indices) {
          if(foundone == false){
            val pos = LeftP(i)
            substitute.apply(pos)(sq) match {
              case Some(_) =>
                res = applyrule(nd,pos,substitute) match { case Some(lst) => lst
                                                          case None => Nil};
                foundone = true;
                ()
              case None => 
                ()
            }
          }
        }

        res

      case _ => Nil
    }
  }




  def arithT : Tactic = new Tactic("arithmetic") {
    def apply(nd: OrNode): List[NodeID] = {
      submitproc(nd, "math")
      Nil
    }

  }







  val alpha = List(andLeft, impRight, allRight)

  val alphaT : Tactic = new Tactic("alpha") {
    def apply(nd: OrNode) = 
      trylistofrules(alpha,nd)._2
  }

  val beta = List(andRight, orLeft, impLeft)

  val betaT : Tactic = new Tactic("beta") {
    def apply(nd: OrNode) = 
      trylistofrules(beta,nd)._2
  }


  val closeOrArithT : Tactic = new Tactic("close") {
    def apply(nd: OrNode) = {
      val (fo,r) = trylistofrules(List(close), nd)
      if(fo) r 
      else arithT.apply(nd)

    }
  }



  val alleasyT: Tactic = composeT(repeatT(eitherT(hpeasyT, alphaT)),
                                   composeT(repeatT(substT),
                                     composeT(repeatT(betaT),
                                           closeOrArithT)))

  def getOpenLeaves(nd: ProofNode) : List[OrNode] = {
    val kds = nd.children.map(getnode)
    (kds, nd.status, nd) match {
      case (Nil,Open, nd1@OrNode(_,_)) =>
        List(nd1)
      case _ =>
        val lvs = kds.map(getOpenLeaves).flatten
        lvs
    }
    
  }


  val applyToLeavesT : Tactic => Tactic = tct =>
     new Tactic("applyToLeavesT " + tct) {
       def apply(nd: OrNode): List[NodeID] = {
         val lvs = getOpenLeaves(rootNode)
         val rs = lvs.map(tct).flatten
         rs
       }
     }

  val nullarizeT : Tactic = 
    new Tactic("nullarize") {
      

      import Prover._

      def getunaryfn(tm: Term) : List[String] = tm match {
        case Fn(f, List(arg)) => List(f)
        case _ => Nil
      }


      def apply(nd: OrNode): List[NodeID] = {
        val Sequent(c,s) = nd.goal
        val fms = c ++ s
        val unaryfns = fms.map(fm => 
                              overterms_Formula(tm => (b:List[String]) => 
                                              getunaryfn(tm) ++ b,
                                                fm, Nil)).flatten.distinct
        println("unaryfns: " + unaryfns)
        val rls = unaryfns.map(s => nullarize(s))
        trylistofrules(rls,nd)._2        
        
      }
    }


}
