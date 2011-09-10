package DLBanyan


object Tactics {

  import Nodes._
  import TreeActions._
  import RulesUtil._
  import Rules._

  
  // A tactic returns a list of the new open leaves that it spawns.

  abstract class Tactic(name: String) 
         extends ((OrNode) =>  Option[List[NodeID]]) {
    override def toString: String = {
      name
    }
    def * : Tactic = repeatT(this)  
    def | (alternative : =>Tactic) = eitherT(this, alternative)
    def ~ (continued : =>Tactic) = composeT(this, continued)
    def & (continued : =>Tactic) = composeT(this, continued)
    def < (tcts : Tactic *) = branchT(this, tcts.toList)
  }


  def trylistofrules(rs: List[ProofRule], nd: OrNode) 
         : Option[List[NodeID]] = {
           val sq = nd.goal;
           var res: Option[List[NodeID]] = None;
   
           for (p <- positions(sq)) {
             for(r <- rs) {
               if(res == None){
            
                val res0 = r.apply(p)(sq);
                res0 match {
                  case Some(_) =>
                    res = applyrule(nd,p,r) 
                    ()
                  case None => 
                    ()
                }
               }
             }
           }
           res
         }

  val trylistofrulesT : List[ProofRule] => Tactic = rls =>
    new Tactic("trylist " + rls) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        trylistofrules(rls, nd)
      }
    }

  val tryruleT : ProofRule => Tactic = rl =>
    new Tactic("tryrule " + rl) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        trylistofrules(List(rl), nd)
      }
    }

  val tryruleatT : ProofRule => Position => Tactic = rl => pos =>
    new Tactic("tryruleat " + rl +  " " + pos ) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val res0 = rl.apply(pos)(nd.goal)
        res0 match {
          case Some(_) =>
            applyrule(nd,pos,rl) 
          case None =>
            None
        }
      }
    }

  val tryrulematchT : ProofRule => Formula => Tactic = rl => fm =>
    new Tactic("tryrulematch " + rl +  " " + fm ) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val Sequent(sig, cs, ss) = nd.goal
        val pnc = cs.indexOf(fm)
        val pns = ss.indexOf(fm)
        (pnc,pns) match { 
          case (-1,-1) => None
          case (-1, pn) => 
            applyrule(nd,RightP(pn),rl) 
          case (pn, _) => 
            applyrule(nd,LeftP(pn),rl) 
        }
      }
    }


  val tryruleunifyT : ProofRule => Formula => Tactic = rl => fm =>
    new Tactic("tryruleunify " + rl +  " " + fm ) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val sq@Sequent(sig, cs, ss) = nd.goal
        for(p <- positions(sq)) {
           Prover.unify(lookup(p,sq), fm) match  {
             case None => ()
             case Some(_) => return tryruleatT(rl)(p)(nd)
           }
        }
        return None
      }
    }

  val tryrulepredT : ProofRule
                        => (Formula => Boolean) => Tactic = 
    rl => pred =>
    new Tactic("tryrulepred " ) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val sq@Sequent(sig, cs, ss) = nd.goal
        for(p <- positions(sq)) {
          val fm = lookup(p,sq)
          if(pred(fm)){
            return tryruleatT(rl)(p)(nd)
          }
        }
        return None

      }
    }



  def usehintsT(pos: Position): Tactic = new Tactic("usehints") {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Modality(Box,Loop(hp, True, inv_hints), phi) => 
        val rules = inv_hints.map(loopInduction)
        // XXX be smarter about success and failure.
        Some(rules.map(r => applyrule(nd, pos, r)).flatten.flatten)
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
      // XXX
        Some(sol_res1 ++ sol_res2 ++ inv_res)
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
        Some(sol_res1 ++ sol_res2)

        
      case _ => None
    }
  }

  def diffsolveT(pos: Position, md: DiffSolveMode): Tactic = 
      new Tactic("diffsolveT " + md) {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Modality(Box,Evolve(derivs,h,inv_hints,sols), phi) =>
        val sol_rule1 = diffSolve(md)(sols)
        applyrule(nd,pos,sol_rule1) 
      case Modality(Box,EvolveQuantified(i,c,vs,h,sols), phi) =>
        val sol_rule1 = qDiffSolve(md)(sols)
        applyrule(nd,pos,sol_rule1)         
      case _ => None
    }
  }


  val hpeasy = List(seq, choose, check, 
                    assign, assignAnyRight, qassign,
                    diffClose
                  )

  val hpalpha = List(seq, check, 
                    assign, assignAnyRight, qassign, choose
                  )

  val needhints = List(loopInduction, diffStrengthen)


  def composeT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("compose " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val mbe_newnds = t1(nd)
        mbe_newnds match {
          case None => None
          case Some(newnds) => 
           val nnds: List[NodeID] = 
             newnds.map(c => 
              {getnodethen(c,gotonode _);
               hereNode match {
                 case ornd@OrNode(_,_) =>
                   t2(ornd)
                 case _ => None
               }}).flatten.flatten
           // XXX think about success and failure
           Some(nnds) 
        }

      }

    }

  val unitT : Tactic = 
    new Tactic("unit") {
      def apply(nd: OrNode) = {
        Some(List(nd.nodeID))
      }
    }

  val nilT : Tactic = 
    new Tactic("nil") {
      def apply(nd: OrNode) = {
        None
      }
    }

  def composelistT(tcts : Tactic * ) : Tactic = 
    tcts.toList.foldRight(unitT)( (t1,t2) => composeT(t1,t2)  )



  // do t1. Then, if no new nodes, do t2.
  //@todo it could make sense to optimize for special case t1=nilT or t2=nilT or, instead, optimize eitherlistT to avoid nilT except for empty list
  def eitherT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("either " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) = {
        val nds = t1.apply(nd);
        nds match {
          case None => 
            t2.apply(nd)
          case _ => 
            nds
        }
        
      }
    }

  def eitherlistT(tcts : Tactic *) : Tactic = 
    tcts.toList.foldRight(nilT)( (t1,t2) => eitherT(t1,t2)  )


  val hpeasyT : Tactic = new Tactic("hpeasy") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(sig, c,List(s)) =>
        // try all the box hp easy rules
        val pos = RightP(0)
        eitherT(trylistofrulesT(hpeasy),usehintsT(pos))(nd) 
      case _ => None
    }
  }


  def repeatT(t: Tactic) : Tactic = new Tactic("repeat " + t.toString) {
    def apply(nd: OrNode) = {
      t(nd) match {
        case None => Some(List(nd.nodeID))
        case Some(newnds) => 
          Some(newnds.map( 
            c => {getnodethen(c,gotonode _);
                  hereNode match {
                    case ornd@OrNode(_,_) =>
                      apply(ornd)
                    case _ => None
                  }
                }).flatten.flatten)
      }
    }

  }



  val substT : Tactic = new Tactic("substitute") {
    def apply(nd: OrNode): Option[List[NodeID]] = nd.goal match {
      case sq@Sequent(sig, c,s) =>

      
        for (i <- c.indices) {
            val pos = LeftP(i)
            substitute.apply(pos)(sq) match {
              case Some(_) =>
                 return applyrule(nd,pos,substitute);
                ()
              case None => 
                ()
            }
        }
        

        return None

      case _ => None
    }
  }




  def arithT : Tactic = new Tactic("arithmetic") {
    def apply(nd: OrNode): Option[List[NodeID]] = {
      if(submitproc(nd, "math")){
        Some(Nil)
      }else {
        None
      }
    }

  }




  val alpha = List(andLeft, impRight, allRight, orRight, not)

  val alphaT : Tactic = new Tactic("alpha") {
    def apply(nd: OrNode) = 
      trylistofrules(alpha,nd)
  }

  val hpalphaT : Tactic = new Tactic("hpalpha") {
    def apply(nd: OrNode) = 
      trylistofrules(hpalpha ++ alpha,nd)
  }

  val hpalpha1T = eitherT(hpalphaT, alphaT)

  val beta = List(andRight, orLeft, impLeft)

  val betaT : Tactic = new Tactic("beta") {
    def apply(nd: OrNode) = 
      trylistofrules(beta,nd)
  }


  val nonarithcloseT = 
    trylistofrulesT(List(close,identity))

  val closeOrArithT = eitherT(trylistofrulesT(List(close, identity)),
                              arithT)


  
  // lazy arithmetic
  //@todo could add cheap close earlier.
  val alleasyT: Tactic = composelistT(repeatT(eitherT(hpeasyT, alphaT)),
                                      repeatT(substT),
                                      repeatT(eitherT(alphaT,betaT)),        
                                      closeOrArithT)

  def getOpenLeaves(nd: ProofNode) : List[OrNode] = {
    val kds = nd.getChildren.map(getnode)
    (kds, nd.getStatus, nd) match {
      case (Nil,Open, nd1@OrNode(_,_)) =>
        List(nd1)
      case _ =>
        val lvs = kds.map(getOpenLeaves).flatten
        lvs
    }
    
  }


  val applyToLeavesT : Tactic => Tactic = tct =>
     new Tactic("applyToLeavesT " + tct) {
       def apply(nd: OrNode): Option[List[NodeID]] = {
         val lvs = getOpenLeaves(rootNode)
         val rs = lvs.map(tct).flatten.flatten
         Some(rs)
       }
     }


  val nullarizeT : Tactic = 
    new Tactic("nullarize") {
      import Prover._
      def getunaryfn(tm: Term) : List[Term] = tm match {
        case Fn(f, List(arg)) if f != "-" => List(tm)
        case Fn(f, args) => args.map(getunaryfn).flatten
        case _ => Nil
      }

      def apply(nd: OrNode): Option[List[NodeID]] = {
        val Sequent(sig, c, s) = nd.goal
        val fms = c ++ s
        val unaryfns = fms.map(fm => 
                              overterms_Formula(tm => (b:List[Term]) => 
                                              getunaryfn(tm) ++ b,
                                                fm, Nil)).flatten.distinct
        println("unaryfns: " + unaryfns)
        val rls = unaryfns.map(tm => unsubstitute(tm))
        trylistofrules(rls, nd)
      }
    }

  val instantiateAuxT : Sort => Term => Formula => Tactic = srt => tm => fm => 
    new Tactic("instantiateAux") {
      def apply(nd: OrNode): Option[List[NodeID]] = {
        val Sequent(sig,cs,ss) = nd.goal
        val pn = cs.indexOf(fm)
        if(pn == -1) None
        else { 
          RulesUtil.lookup(LeftP(pn), nd.goal) match {
            case Quantifier(Forall, srt1, _,_) if srt == srt1 =>
              applyrule(nd,LeftP(pn),allLeft(tm))
            case Quantifier(Forall, srt1, _,_)  => Some(List(nd.nodeID))
            case _ => None
          }
        }

      }
      
    }


  def findunivs(srt: Sort, sq: Sequent): List[Formula] = sq match {
    case Sequent(sig,cs,ss) =>
      var res: List[Formula] = Nil
      for(c <- cs) {
        c match {
          case Quantifier(Forall,srt1,_,_) if srt1 == srt =>
            res = c::res
            ()
          case _ =>
            ()
        }
      }
    res
  }

  def findSingleUnivs(srt: Sort, sq: Sequent): List[Formula] = sq match {
    case Sequent(sig,cs,ss) =>
      var res: List[Formula] = Nil
      for(c <- cs) {
        c match {
          case Quantifier(Forall, srt1, _,
                          Quantifier(Forall, _, _, _))  =>
            ()
          case Quantifier(Forall,srt1,_,_) if srt1 == srt =>
            res = c::res
            ()
          case _ =>
            ()
        }
      }
    res
  }


  val instantiateT : Sort => List[Term] => Tactic = srt => tms => 
    new Tactic("instantiate") {
      def apply(nd: OrNode): Option[List[NodeID]] = {
        val Sequent(sig,_,_) = nd.goal
        val fms = findunivs(srt,nd.goal)
        var tct1 = unitT
        for(tm <- tms) {
          if(Prover.infersort(sig, tm) == srt){
            tct1 = 
              fms.foldRight(tct1)((fm1,rt) => 
                composeT(instantiateAuxT(srt)(tm)(fm1),rt))          
          }
        }
        tct1(nd)
      }
    }

  val instantiatesinglesT : Sort => List[Term] => Tactic = srt => tms => 
    new Tactic("instantiate") {
      def apply(nd: OrNode): Option[List[NodeID]] = {
        val Sequent(sig,_,_) = nd.goal
        val fms = findSingleUnivs(srt,nd.goal)
        var tct1 = unitT
        for(tm <- tms) {
          if(Prover.infersort(sig, tm) == srt){
            tct1 = 
              fms.foldRight(tct1)((fm1,rt) => 
                composeT(instantiateAuxT(srt)(tm)(fm1),rt))          
          }
        }
        tct1(nd)
      }
    }

 val instantiatebyT : Sort => List[(String, List[String])] => Tactic = srt => alist =>
   new Tactic("instantiate by") {
     def apply(nd: OrNode): Option[List[NodeID]] = {
       val Sequent(sig,_,_) = nd.goal
       val sig1 =
         sig.filter((kv) => kv._2 match { case (Nil, srt1) if srt == srt1 => true
                                         case _ => false}) 
       val insts = sig1.keys.toList
       val fms = findunivs(srt, nd.goal)
       var tcts : List[Tactic] = Nil
       for (fm <- fms) {
         fm match {
           case Quantifier(Forall, s, i, fm0) =>
             Prover.assoc(Prover.ununiqify(i), alist) match {
               case None => ()
               case Some(js) => 
                 for (j <- js) {
                   tcts = 
                     insts.filter(x => Prover.ununiqify(x) == j).map(x =>
                       instantiateAuxT(srt)(Fn(x,Nil))(fm)) ++ tcts
                 }
             }
           case _ => ()
         }
       }
       if (tcts.length == 0) {
         None
       } else {
         val tct = tcts.foldRight(unitT)(composeT)
         val hidetct = fms.map(fm => tryrulematchT(hide)(fm)).foldRight(unitT)(composeT)
         composeT(tct, hidetct)(nd)
       }
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

  val instantiate0T : Sort => Tactic = srt => new Tactic("instantiate0") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val idcs = findidx(nd.goal)
      val tct1 =             
        idcs.foldRight(unitT)((idx,rt) => 
          composeT(instantiateT(srt)(List(idx._1,idx._2)),rt))
      tct1(nd)
    }
  }

  val instantiate1T : Sort => Tactic = srt => new Tactic("instantiate1") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val idcs = findidx(nd.goal)
      val uvs = findunivs(srt,nd.goal)
      val tct1 =             
        idcs.foldRight(unitT)((idx,rt) => 
          composeT(instantiateT(srt)(List(idx._1,idx._2)),rt))
      val tct2 =             
        uvs.foldRight(unitT)((fm1,rt) => 
          composeT(tryrulematchT(hide)(fm1),rt));
      composeT(tct1,tct2)(nd)
    }
  }


  val instantiate2T : Term => Term => Tactic =  tm1 => tm2 => 
    new Tactic("instantiate2") {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val sq = nd.goal
        for(p <- positions(sq)){
          lookup(p,sq) match {
            case fm@Quantifier(Forall, srt1, i1, 
                               fm1@Quantifier(Forall, srt2, i2, fm2)) =>
                                 return composelistT(
                                   tryruleatT(allLeft(tm1))(p),
                                   tryruleunifyT(allLeft(tm2))(fm1),
                                   tryruleunifyT(hide)(fm1)
                                 )(nd)
            case _ => ()

          }

        }
        return None
      }
    }

  val instantiate3T : Tactic  =new Tactic("instantiate3") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val idcs = findidx(nd.goal)
      val tct1 =             
        idcs.foldRight(unitT)((idx,rt) => 
          composeT(instantiate2T(idx._1)(idx._2),rt))
      tct1(nd)
    }
  }

  val instantiate4T : Tactic  =new Tactic("instantiate4") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val idcs = findidx(nd.goal)
      val tct1 =             
        idcs.foldRight(unitT)((idx,rt) => 
          composeT(instantiate2T(idx._2)(idx._1),rt))
      tct1(nd)
    }
  }

  val instantiate5T : Sort => Tactic  = srt => new Tactic("instantiate5 " + srt) {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val Sequent(sig,s,c) = nd.goal
      val sig1 = sig.filter((kv) => kv._2 match { case (Nil, srt1) if srt == srt1 => true
                                                case _ => false})
      val tms = 
        sig1.keys.toList.sortWith((s1,s2) => 
          s1.compareTo(s2) < 0 ).map( k => (Fn(k,Nil): Term) )
      instantiateT(srt)(tms)(nd)
    }
  }


  val instantiatesinglesofT : Sort => Tactic = srt => new Tactic("instantiate5 " + srt) {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val Sequent(sig,s,c) = nd.goal
      val sig1 = sig.filter((kv) => kv._2 match { case (Nil, srt1) if srt == srt1 => true
                                                case _ => false})
      val tms = 
        sig1.keys.toList.sortWith((s1,s2) => 
          s1.compareTo(s2) < 0 ).map( k => (Fn(k,Nil): Term) )
      instantiatesinglesT(srt)(tms)(nd)
    }
  }

  

  val hideunivsT : Sort => Tactic = srt => new Tactic("hideunivs") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val fms = findunivs(srt,nd.goal)
      val tct1 =             
        fms.foldRight(unitT)((fm1,rt) => 
          composeT(tryrulematchT(hide)(fm1),rt));
      tct1(nd)
      
    }
  }

  val hidedoublequantT : Tactic = 
    new Tactic("hidedoublequant") {
      def apply(nd: OrNode) : Option[List[NodeID]] = {
        val sq = nd.goal
        for(p <- positions(sq)){
          lookup(p,sq) match {
            case fm@Quantifier(Forall, srt1, i1, 
                               fm1@Quantifier(Forall, srt2, i2, fm2)) =>
                                 return tryruleatT(hide)(p)(nd);

            case _ => ()

          }

        }
        return None
      }
    }



  def branchT(tct: Tactic, tcts: List[Tactic]) : Tactic = 
    new Tactic("branch " + tct + " " + tcts) {

    def apply(nd: OrNode) : Option[List[NodeID]] = {
      tct(nd) match {
        case None => None
        case Some(newndids) => 
          val newnds = newndids.map(getnode)
          val ndstcts = tcts.zip(newnds)
          val newnds1 = ndstcts.map(  x => 
              x._2 match {
                case ornd@OrNode(_,_) => (x._1)(ornd)
                case _ => None } ) .flatten.flatten
      
        Some(newnds1)
      }

    }

    }

  



  def hidecantqeT : Tactic = new Tactic("hidecantqe"){
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val sq@Sequent(sig, c,s) = nd.goal
      var cantqe: List[Formula] = Nil
      for(p <- positions(sq)) {
        val fm = lookup(p,sq)
        cantqe = if(Prover.canQE(fm, sig)) cantqe else fm::cantqe
      }
      println("cantqe: " + cantqe);

      val tct = cantqe.foldRight(unitT)((fm1,rt) 
                                        => composeT(tryrulematchT(hide)(fm1),
                                                    rt));
      tct(nd)
    }
  }

  val hidethencloseT = composeT(hidecantqeT, closeOrArithT)

  sealed abstract class CutType
  case object DirectedCut extends CutType
  case object StandardCut extends CutType
  case object StandardKeepCut extends CutType

  def cutT(ct: CutType, cutout: Formula, cutin: Formula): Tactic 
  = new Tactic("cut " + ct) {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
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
        case None => None
        case Some(subs) =>
          val cutin1 = Prover.simul_substitute_Formula(subs.toList, cutin)
          val rl = ct match {
            case DirectedCut => directedCut
            case StandardCut => cut
            case StandardKeepCut => cutKeepSucc
          }
          tryruleatT(rl(cutin1))(LeftP(foundidx))(nd)
      }   
    }
  }


  val vacuousT: Tactic 
  = new Tactic("vacuous") {
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val Sequent(sig,cs,ss) = nd.goal
      var res:Option[List[NodeID]] = None
      for (i <- cs.indices){
        res match {
          case Some(_) => ()
          case None =>
            cs(i) match {
              case Binop(Imp, 
                         Not(Atom(R("=", List(f1,f2)))),
                         fm) if f1 == f2 =>
                           return tryruleatT(hide)(LeftP(i))(nd)
              case Binop(Imp, 
                         Binop(And, _,
                               Not(Atom(R("=", List(f1,f2))))),
                         fm) if f1 == f2 =>
                           return tryruleatT(hide)(LeftP(i))(nd)
              case Binop(Imp, 
                         Binop(And,
                               Not(Atom(R("=", List(f1,f2)))),
                               _),
                         fm) if f1 == f2 =>
                           return tryruleatT(hide)(LeftP(i))(nd)
              case Binop(Imp, 
                         Binop(And,
                               Binop(And,
                                     Not(Atom(R("=", List(f1,f2)))),
                                     _),
                               _),
                         fm) if f1 == f2 =>
                           return tryruleatT(hide)(LeftP(i))(nd)
              case Binop(Imp, 
                         Binop(And,
                               Binop(And, _ ,
                                     Not(Atom(R("=", List(f1,f2))))
                                     ),
                               _),
                         fm) if f1 == f2 =>
                           return tryruleatT(hide)(LeftP(i))(nd)
              case _ => 
                ()
            }
        }
      }
      res
          
      
    }
  }

  val hidenotmatchT : List[Formula] => Tactic =  fms => {
    val nomatches : Formula => Boolean   = fm => {
      val ms = fms.map(fm1 => Prover.unify(fm,fm1) )
//      println("ms= " + ms)
      (fms.forall(fm1 => Prover.unify(fm,fm1) == None  ))
    }
    tryrulepredT(hide)(nomatches)
  }

  val hidematchT : List[Formula] => Tactic =  fms => {
    val matches : Formula => Boolean   = fm => {
      val ms = fms.map(fm1 => Prover.unify(fm,fm1) )
      !(fms.forall(fm1 => Prover.unify(fm,fm1) == None  ))
    }
    tryrulepredT(hide)(matches)
  }


  val dedupT : Tactic = new Tactic("dedup"){
    def apply(nd: OrNode) : Option[List[NodeID]] = {
      val Sequent(sig,cs,ss) = nd.goal
      hidematchT(cs.diff(cs.distinct))(nd)
    }
  }



  val impleftknownT : Tactic = new Tactic("impleftknown") {
    def apply(nd : OrNode) : Option[List[NodeID]] = {
      val Sequent(sig,cs,ss) = nd.goal
      for(i <- cs.indices) {
        cs(i) match {
          case Binop(Imp,Atom(R("=",List(t1,t2))) ,f2) if t1 == t2 =>
            return (tryruleatT(impLeft)(LeftP(i))<(
              unitT,
              nonarithcloseT
            ))(nd)

          case Binop(Imp,f1,f2) =>
            for(c2 <- cs) {
              if (f1 == c2 ){
                return (tryruleatT(impLeft)(LeftP(i))<(
                  unitT,
                  nonarithcloseT
                ))(nd)
              } else {
                ()
              }
            }
          case _ =>
          ()
        }
      }
      return None
    }
  }


}
