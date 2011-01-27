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
    def * : Tactic = repeatT(this)  
    def | (alternative : Tactic) = eitherT(this, alternative)
    def & (continued : Tactic) = composeT(this, continued)
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

  val tryruleT : ProofRule => Tactic = rl =>
    new Tactic("tryrule " + rl) {
      def apply(nd: OrNode) : List[NodeID] = {
        trylistofrules(List(rl), nd)._2
      }
    }

  val tryruleatT : ProofRule => Position => Tactic = rl => pos =>
    new Tactic("tryruleat " + rl +  " " + pos ) {
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

  val tryrulematchT : ProofRule => Formula => Tactic = rl => fm =>
    new Tactic("tryrulematch " + rl +  " " + fm ) {
      def apply(nd: OrNode) : List[NodeID] = {
        val Sequent(sig, cs, ss) = nd.goal
        val pnc = cs.indexOf(fm)
        val pns = ss.indexOf(fm)
        (pnc,pns) match { 
          case (-1,-1) => Nil
          case (-1, pn) => 
            applyrule(nd,RightP(pn),rl) match { case Some(lst) => lst
                                                 case None => Nil};
          case (pn, _) => 
            applyrule(nd,LeftP(pn),rl) match { case Some(lst) => lst
                                               case None => Nil};


        }
      }
    }


  def usehintsT(pos: Position): Tactic = new Tactic("usehints") {
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
      case Modality(Box,EvolveQuantified(i,c,vs,h,sols), phi) =>
        val sol_rule1 = qDiffSolve(Endpoint)(sols)
        val sol_rule2 = qDiffSolve(Standard)(sols)
        val sol_res1 = applyrule(nd,pos,sol_rule1) match {
          case None => Nil
          case Some(lst) => lst
        }
        val sol_res2 = applyrule(nd,pos,sol_rule2) match {
          case None => Nil
          case Some(lst) => lst
        } 
        sol_res1 ++ sol_res2

        
      case _ => Nil
    }
  }

  def diffsolveT(pos: Position, md: DiffSolveMode): Tactic = new Tactic("diffsolveT " + md) {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Modality(Box,Evolve(derivs,h,inv_hints,sols), phi) =>
        val sol_rule1 = diffSolve(md)(sols)
        val sol_res1 = applyrule(nd,pos,sol_rule1) match {
          case None => Nil
          case Some(lst) => lst
        }
        sol_res1
      case Modality(Box,EvolveQuantified(i,c,vs,h,sols), phi) =>
        val sol_rule1 = qDiffSolve(md)(sols)
        val sol_res1 = applyrule(nd,pos,sol_rule1) match {
          case None => Nil
          case Some(lst) => lst
        }
        sol_res1

        
      case _ => Nil
    }
  }


  val hpeasy = List(seq, choose, check, 
                    assign, assignAnyRight, qassign,
                    diffClose
                  )

  val hpalpha = List(seq, check, 
                    assign, assignAnyRight, qassign
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

  val unitT : Tactic = 
    new Tactic("unit") {
      def apply(nd: OrNode) = {
        List(nd.nodeID)
      }
    }

  val nilT : Tactic = 
    new Tactic("nil") {
      def apply(nd: OrNode) = {
        Nil
      }
    }

  def composelistT(tcts : List[Tactic]) : Tactic = 
    tcts.foldRight(unitT)( (t1,t2) => composeT(t1,t2)  )



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

  def eitherlistT(tcts : List[Tactic]) : Tactic = 
    tcts.foldRight(nilT)( (t1,t2) => eitherT(t1,t2)  )


  val hpeasyT : Tactic = new Tactic("hpeasy") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(sig, c,List(s)) =>
        // try all the box hp easy rules
        val pos = RightP(0)
        val (_,nds1) = trylistofrules(hpeasy, nd)
        val nds2 = usehintsT(pos)(nd)
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
      case sq@Sequent(sig, c,s) =>

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







  val alpha = List(andLeft, impRight, allRight, orRight, not)

  val alphaT : Tactic = new Tactic("alpha") {
    def apply(nd: OrNode) = 
      trylistofrules(alpha,nd)._2
  }

  val hpalphaT : Tactic = new Tactic("hpalpha") {
    def apply(nd: OrNode) = 
      trylistofrules(hpalpha ++ alpha,nd)._2
  }

  val hpalpha1T = eitherT(hpalphaT, alphaT)

  val beta = List(andRight, orLeft, impLeft)

  val betaT : Tactic = new Tactic("beta") {
    def apply(nd: OrNode) = 
      trylistofrules(beta,nd)._2
  }


  val nonarithcloseT = 
    trylistofrulesT(List(close,identity))

  val closeOrArithT : Tactic = new Tactic("close") {
    def apply(nd: OrNode) = {
      val (fo,r) = trylistofrules(List(close, identity), nd)
      if(fo) r 
      else arithT.apply(nd)

    }
  }



  val alleasyT: Tactic = composelistT(List(repeatT(eitherT(hpeasyT, alphaT)),
                                           repeatT(substT),
                                           repeatT(eitherT(alphaT,betaT)),        
                                           closeOrArithT))

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
        case Fn(f, args) => args.map(getunaryfn).flatten
        case _ => Nil
      }


      def apply(nd: OrNode): List[NodeID] = {
        val Sequent(sig,c,s) = nd.goal
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


  val instantiateAuxT : Term => Formula => Tactic = tm => fm => 
    new Tactic("instantiateAux") {
      def apply(nd: OrNode): List[NodeID] = {
        val Sequent(sig,cs,ss) = nd.goal
        val pn = cs.indexOf(fm)
        if(pn == -1) Nil
        else applyrule(nd,LeftP(pn),allLeft(tm)) match { case Some(lst) => lst
                                                        case None => Nil};

      }
      
    }


  def findunivs(sq: Sequent): List[Formula] = sq match {
    case Sequent(sig,cs,ss) =>
      var res: List[Formula] = Nil
      for(c <- cs) {
        c match {
          case Quantifier(Forall,_,_,_) =>
            res = c::res
            ()
          case _ =>
            ()
        }
      }
    res
  }

  val instantiateT : List[Term] => Tactic = tms => 
    new Tactic("instantiate") {
      def apply(nd: OrNode): List[NodeID] = {
        val fms = findunivs(nd.goal)
        var tct1 = unitT
        for(tm <- tms) {
          tct1 = 
            fms.foldRight(tct1)((fm1,rt) => 
              composeT(instantiateAuxT(tm)(fm1),rt))          
        }
        tct1(nd)
      }
    }


  def findidx(sq: Sequent): List[(Term,Term)] = sq match {
    case Sequent(sig,cs,ss) =>
      var res: List[(Term,Term)] = Nil
      for(c <- cs) {
        c match {
          case Not(Atom(R("=", List(t1,t2)))) => 
            res = (t1,t2)::res
            ()
          case _ =>
            ()
        }
      }
      for(s <- ss) {
        s match {
          case Atom(R("=", List(t1,t2))) => 
            res = (t1,t2)::res
            ()
          case _ =>
            ()
        }
      }
    res
  }

  val instantiate0T : Tactic = new Tactic("instantiate0") {
    def apply(nd: OrNode) : List[NodeID] = {
      val idcs = findidx(nd.goal)
      val tct1 =             
        idcs.foldRight(unitT)((idx,rt) => 
          composeT(instantiateT(List(idx._1,idx._2)),rt))
      tct1(nd)
    }
  }


  val hideunivsT : Tactic = new Tactic("hideunivs") {
    def apply(nd: OrNode) : List[NodeID] = {
      val fms = findunivs(nd.goal)
      val tct1 =             
        fms.foldRight(unitT)((fm1,rt) => 
          composeT(tryrulematchT(hide)(fm1),rt));
      tct1(nd)
      
    }
  }


  def branchT(tct: Tactic, tcts: List[Tactic]) : Tactic = 
    new Tactic("branch " + tct + " " + tcts) {

    

    def apply(nd: OrNode) : List[NodeID] = {
      val newnds = tct(nd).map(getnode)
      
      val ndstcts = tcts.zip(newnds)
      val newnds1 = ndstcts.map(  x => 
            x._2 match {
              case ornd@OrNode(_,_) => (x._1)(ornd)
              case _ => Nil } ) .flatten
      
      newnds1

    }

  }



  def hidecantqeT : Tactic = new Tactic("hidecantqe"){
    def apply(nd: OrNode) : List[NodeID] = {
      val sq@Sequent(sig, c,s) = nd.goal
      var cantqe: List[Formula] = Nil
      for(p <- positions(sq)) {
        val fm = lookup(p,sq)
        cantqe = if(Prover.canQE(fm, sig)) cantqe else fm::cantqe
      }

      val tct = cantqe.foldRight(unitT)((fm1,rt) 
                                        => composeT(tryrulematchT(hide)(fm1),
                                                    rt));
      tct(nd)
    }
  }


  val hidethencloseT = composeT(hidecantqeT, closeOrArithT)


  def cutT(cutout: Formula, cutin: Formula): Tactic 
  = new Tactic("cut") {
    def apply(nd: OrNode) : List[NodeID] = {
      println("trying cutT on " + nd.nodeID)
      val Sequent(sig,cs,ss) = nd.goal
      var mbesubs : Option[Prover.Subst] = None;
      var foundidx = -1;
      for (i <- cs.indices){
        if(mbesubs == None) {
          Prover.unify(cs(i),cutout) match {
            case None => 
              println("didn't match here: " + i)
            case Some(subs) => 
              mbesubs = Some(subs)
              foundidx = i;
          }
        }
      }
      mbesubs match {
        case None => Nil
        case Some(subs) =>
          val cutin1 = Prover.simul_substitute_Formula(subs.toList, cutin)
          tryruleatT(directedCut(cutin1))(LeftP(foundidx))(nd)
      }   
    }
  }


  val vacuousT: Tactic 
  = new Tactic("vacuous") {
    def apply(nd: OrNode) : List[NodeID] = {
      val Sequent(sig,cs,ss) = nd.goal
      var res:List[NodeID] = Nil
      var foundone = false
      for (i <- cs.indices){
        if(foundone == false){
          cs(i) match {
              case Binop(Imp, 
                         Not(Atom(R("=", List(f1,f2)))),
                         fm) if f1 == f2 =>
                           res = tryruleatT(hide)(LeftP(i))(nd)
                           () 
              case _ => 
                ()
          }
        }
      }
      res
          
      
    }
  }


}
