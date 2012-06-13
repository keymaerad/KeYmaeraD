/**
 * This file is soundness critical. Don't touch without review!
 * @soundness
 */
package KeYmaeraD


object RulesUtil {

  abstract class Position 
  case class LeftP(n: Int) extends Position
  case class RightP(n: Int) extends Position
//  case object Outer extends Position


  type ProofRuleResult =  Option[(List[Sequent], List[String])]

  // A proof rule returns None if it does not apply.
  // Otherwise it returns a list of subgoals
  // and a list of new free variables.
  abstract class ProofRule(name: String) extends 
    ((Position) =>   
        (Sequent) =>  
          ProofRuleResult) {
            override def toString: String = {
              name
            }
          }
  
  class LookupError() extends Exception()


  def positions(sq : Sequent) : List[Position] = sq match {
    case Sequent(fs,c,s) =>
      c.indices.toList.map(i => LeftP(i)) ++ 
       s.indices.toList.map(i => RightP(i))
  }

  def replacelist[A](i: Int, lst: List[A], a: A): List[A] = lst match {
    case Nil => Nil
    case x::xs =>
      if(i <= 0) a::xs
      else x::replacelist(i-1,xs,a)      
  }

  def splicelist[A](i: Int, lst: List[A], a: List[A]): List[A] = lst match {
    case Nil => Nil
    case x::xs =>
      if(i <= 0) a ++ xs
      else x::splicelist(i-1,xs,a)      
  }

  //remove the ith element
  def removelist[A](i: Int, lst: List[A]): List[A] = lst match {
    case Nil => Nil
    case x::xs =>
      if(i <= 0) xs
      else x::removelist(i-1,xs)      
  }


  def replace(p: Position, s: Sequent,fm : Formula): Sequent = (p,s) match {
    case (LeftP(n), Sequent(fs,ct,st)) => 
      if(n >= ct.length || n < 0 )
        throw new  LookupError()
      else Sequent(fs,replacelist(n,ct,fm),st)
    case (RightP(n), Sequent(fs,ct,st)) => 
      if(n >= st.length || n < 0 )
        throw new LookupError()
      else Sequent(fs,ct,replacelist(n,st,fm))
  }

  def lookup(p: Position, s: Sequent): Formula = (p,s) match {
    case (LeftP(n), Sequent(fs,ct,st)) => 
      if(n >= ct.length || n < 0 )
        throw new   LookupError()
      else ct.slice(n,n+1).head
    case (RightP(n), Sequent(fs,ct,st)) => 
      if(n >= st.length || n < 0 )
        throw new LookupError()
      else st.slice(n,n+1).head
  }


  def remove(p: Position, s: Sequent): Sequent = (p,s) match {
    case (LeftP(n), Sequent(fs,ct,st)) => 
      if(n >= ct.length || n < 0 )
        throw new  LookupError()
      else Sequent(fs,removelist(n,ct),st)
    case (RightP(n), Sequent(fs,ct,st)) => 
      if(n >= st.length || n < 0 )
        throw new LookupError()
      else Sequent(fs,ct,removelist(n,st))
  }



/*
  def optionbind[A](op:Option[Option[A]]): Option[A] = op match {
    case Some(Some(x)) => Some(x)
    case Some(None) => None
    case None => None
  }

  def extractmap(p: Position, 
                 s: Sequent,
                 f: Formula => Option[Formula]): Option[Sequent] 
   = optionbind(extract(p,s).map(f1 => replacesequent(p,s,f(f1))))

*/

}

object Rules {

  import RulesUtil._

  val close = new ProofRule("close"){ 
    def apply(p: Position) = sq => {
      val Sequent(fs,_,_) = sq
      val fm = lookup(p,sq)
      (p,fm) match {
        case (LeftP(_), False) => 
          Some((Nil,Nil)) // proved!
        case (RightP(_), True) => 
          Some((Nil,Nil)) // proved!
        case (LeftP(n), fm) =>
          if(sq.scdts.exists(fm1 => Prover.alphaeq(fm,fm1)))
            Some((Nil,Nil)) // proved!
          else None
        case (RightP(n), fm) =>
          if(sq.ctxt.exists(fm1 => Prover.alphaeq(fm,fm1)))
            Some((List(Sequent(fs,Nil,List(True))),Nil)) // proved!
          else None
      }
    } 
  }

  val identity = new ProofRule("identity"){
    def apply(p: Position) = sq => {
      val Sequent(fs,_,_) = sq
      val fm = lookup(p,sq)
      (p,fm) match {
        case (RightP(_), Atom(R("=", List(t1,t2)))) if t1 == t2 =>           
          Some((List(Sequent(fs,Nil,List(True))),Nil)) // proved!
        case (LeftP(_), Atom(R("/=", List(t1,t2)))) if t1 == t2 =>           
          Some((List(Sequent(fs,Nil,List(True))),Nil)) // proved!
        case _ => None
      }
    }
  }

  val commuteEquals = new ProofRule("commuteequals"){
    def apply(p: Position) = sq => {
      val Sequent(fs,c,s) = sq
      val fm = lookup(p,sq)
      fm match {
        case (Atom(R("=", List(t1,t2))))  =>           
          val sq1 = replace(p,sq, Atom(R("=", List(t2,t1))))
          Some((List(sq1),Nil)) 
        case (Atom(R("/=", List(t1,t2))))  =>           
          val sq1 = replace(p,sq, Atom(R("/=", List(t2,t1))))
          Some((List(sq1),Nil)) 
        case _ => None
      }
    }
  }

  val hide = new ProofRule("hide") {
    def apply(p:Position) = sq => 
      Some((List(remove(p, sq)), Nil))
  }
   
  //
  // propositional rules
  //

  val andLeft  = new ProofRule("andleft") {
    def apply(p:Position) = sq => (p,sq) match {
      case (LeftP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(And,f1,f2) => 
            val sq1 = Sequent(fs,splicelist(n,c,List(f1,f2)),s)
            Some( (List(sq1),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val andRight  = new  ProofRule("andright") {
    def apply(p:Position) = sq => (p,sq) match { 
      case (RightP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(And,f1,f2) => 
            val sq1 = replace(p,sq,f1)
            val sq2 = replace(p,sq,f2)
            Some( (List(sq1,sq2),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val impRight  = new  ProofRule("impright") {
    def apply(p:Position) = sq => (p,sq) match { 
      case (RightP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(Imp,f1,f2) => 
            val Sequent(fs1,c1,s1) = replace(p,sq,f2)
            Some( (List(Sequent(fs1,f1::c1, s1)),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val impLeft  = new  ProofRule("impleft") {
    def apply(p:Position) = sq => (p,sq) match { 
      case (LeftP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(Imp,f1,f2) => 
            val sq1 = replace(p,sq,f2)
            val Sequent(fs1,c1,s1) = remove(p,sq)
            val sq2 = Sequent(fs1,c1,f1::s1)
            Some( (List(sq1,sq2),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val orRight = new ProofRule("orright") { 
    def apply(p:Position) = sq => (p,sq) match { 
      case (RightP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(Or,f1,f2) => 
            val sq1 = Sequent(fs,c,splicelist(n,s,List(f1,f2)))
            Some( (List(sq1),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val orLeft = new  ProofRule("orleft") {
    def apply(p:Position) = sq => (p,sq) match { 
      case (LeftP(n), Sequent(fs,c,s)) =>
        val fm = lookup(p,sq)
        fm match {
          case Binop(Or,f1,f2) => 
            val sq1 = replace(p,sq,f1)
            val sq2 = replace(p,sq,f2)
            Some( (List(sq1,sq2),Nil))
          case _ => 
            None
        }
      case _ => None
    }
  }

  val not = new ProofRule("not") { 
    def apply(p:Position) = sq => {
      val Sequent(fs,c,s) = sq
      val fm = lookup(p,sq)
      val Sequent(fs1,c1,s1) = remove(p,sq)
      (fm,p) match {
        case (Not(f1),RightP(_)) => 
          Some( (List(Sequent(fs1,f1::c1,s1)),Nil))
        case (Not(f1),LeftP(_)) => 
          Some( (List(Sequent(fs1,c1,f1::s1)),Nil))
        case _ => 
          None
      }
    }
  }

  //
  // quantifier rules
  //


  val allRight = new ProofRule("allright") {
    def apply(p: Position) = sq => (p,sq) match {
      case (RightP(n), Sequent(fs, c,s)) =>
        val fm = lookup(p,sq)
        val fvs = Util.fv(fm).map( x => Var(x))
        (fm) match {
          case Quantifier(Forall, c, v, phi) =>
            val v1 = Prover.uniqify(v)
            val phi1 = Prover.substitute_Formula(v, Fn(v1,fvs), phi)
            val Sequent(fs1,c1,s1) = replace(p,sq, phi1)
            val sq2 = Sequent(fs1.+((v1,(Nil, c) )),
                              c1,s1 )// XXX add args of v1 to signature map
            Some( (List(sq2), Nil))
          case _ => 
            None
        }
      case _ => 
        None
    }

  }



  val allLeft : Term => ProofRule = tm => 
   new ProofRule("allleft") {
    // XXX should also check that that tm has the appropriate sort
    def apply(p: Position) = sq => (p,sq) match {
      case (LeftP(n), Sequent(sig, c,s)) =>
        val fm = lookup(p,sq)
        val srttm = Prover.infersort(sig,tm)
        fm match {
          // first case is an optimization
          case Quantifier(Forall, srt, v, phi) 
             if srt == srttm && Prover.firstorder(phi) =>
            val phi1 = Prover.substitute_Formula(v, tm, phi)
            Some( (List(Sequent(sig, phi1::c,s)), Nil))
          case Quantifier(Forall, srt, v, phi) if srt == srttm =>
            val v1 = Prover.uniqify(v)
            val fv1 = Fn(v1,Nil)
            val phi1 = Prover.substitute_Formula(v, fv1, phi)
            val fm1 = Atom(R("=", List(fv1, tm)))
            Some( (List(Sequent(sig, fm1::phi1::c,s)), Nil))
          case _ =>
            None
        }
      case _ =>
        None
    }
  }
  
  //
  // regular hybrid program rules
  //

  val seq = new ProofRule("seq") {
    def apply(p: Position) = sq => {
      val fm  = lookup(p,sq)
      fm match {
        // Same rule for Box and Diamond.
        case  Modality(mod, Seq(h1,h2), phi) => 
           val fm1 = Modality(mod, h1,
                              Modality(mod, h2, phi))
           val sq1 = replace(p,sq,fm1)
           Some(List(sq1), Nil)
        case _ => None
      }
    }
  }

  val choose = new ProofRule("choose") {
    def apply(p: Position) = sq => {
        val fm = lookup(p, sq)
        fm match {
          case Modality(Box, Choose(h1, h2), phi) => 
            val fm1 = Modality(Box, h1, phi) 
            val fm2 = Modality(Box, h2, phi)
            val sq1 = replace(p, sq, Binop(And, fm1, fm2))
            Some((List(sq1),Nil))
          case Modality(Diamond, Choose(h1, h2), phi) => 
            val fm1 = Modality(Diamond, h1, phi) 
            val fm2 = Modality(Diamond, h2, phi)
            val sq1 = replace(p, sq, Binop(Or, fm1, fm2))
            Some((List(sq1),Nil))
          case _ => 
            None
        }
    }
  }

  val check = new ProofRule("check") {
    def apply(p: Position) = sq => {
        val fm = lookup(p, sq)
        fm match {
          case Modality(Box, Check(fm1), phi) => 
            val fm2 = Binop(Imp, fm1, phi)
            val sq1 = replace(p, sq, fm2)
            Some((List(sq1), Nil))
          case Modality(Diamond, Check(fm1), phi) => 
            val fm2 = Binop(And, fm1, phi)
            val sq1 = replace(p, sq, fm2)
            Some((List(sq1), Nil))
          case _ => 
            None
        }
    }
  }

  //
  // assignment rules
  //

 val assign = new ProofRule("assign") {
    def apply(p: Position) = sq =>   {
      val Sequent(sig, c,s) = sq
      val fm = lookup(p,sq)
      fm match {
        
        // Same rule for Box and Diamond.
        case Modality(_, Assign(vs), phi) =>
          var phi1 = phi;
          var sig1 = sig;
          var c1 = c;
          for(v <- vs) v match {
            case (Fn(vr, Nil), tm) =>
              val vr1 = Prover.uniqify(vr);
              phi1 = Prover.renameFn(vr,vr1,phi1);
              sig1 = sig.get(vr) match {
                case Some(sg) =>
                  sig1.+((vr1, sg))
                case _ => 
                  sig1
              }
              val fm1 = Atom(R("=", List(Fn(vr1, Nil), tm)));

              // order matters! we want p to still point to phi
              c1 = c1 ++ List(fm1);

            case (Fn(vr, List(arg)), tm) =>
              val vr1 = Prover.uniqify(vr)
              phi1 = Prover.renameFn(vr, vr1, phi1);
              val (srt1, sig2) = sig.get(vr) match {
                case Some(sg@(List(srt1), rtn)) =>
                  (srt1, sig1 + ((vr1, sg))   )
                case _ => 
                    (AnySort, sig1)
              }
              sig1 = sig2
              val j = Prover.uniqify("j")
              val fm1 = Atom(R("=", List(Fn(vr1, List(arg)), tm)));
              val fm2 = Quantifier(Forall, srt1, j, 
                                   Binop(Imp,
                                         Not(Atom(R("=", List(Var(j), arg)))),
                                         Atom(R("=", List(Fn(vr1, List(Var(j))),
                                                          Fn(vr, List(Var(j))))))));

              // order matters! we want p to still point to phi
              c1 = c1 ++ List(fm1, fm2);

            case (Fn(vr, _), tm) =>
              throw new Error("Unimplimented: assign to nonunary function")
          }
          val sq1 = replace(p, Sequent(sig1, c1, s), phi1)
          Some((List(sq1), Nil))

        case _ =>
          None
      }
   }
 }

//XXX FIX: what if "i" is not the argument?
 val qassign = new ProofRule("qassign") {
    def apply(p: Position) = sq =>   {
      val Sequent(sig, c, s) = sq
      val fm = lookup(p, sq)
      fm match {
        case Modality(_, AssignQuantified(i, srt, vs), True) =>        
          // an optimization. can be generalized.
          val sq1 = replace(p, sq, True)
          Some((List(sq1), Nil))
        case Modality(_, AssignQuantified(i, srt, vs), phi) => 
          var phi1 = phi;
          var sig1 = sig;
          var c1 = c;
          for(v <- vs) {
              val (Fn(vr, args), tm) = v;
              val vr1 = Prover.uniqify(vr);
              phi1 = Prover.renameFn(vr, vr1, phi1);
              sig1 = sig.get(vr) match {
                case Some(sg) =>
                  sig1.+((vr1, sg))
                case _ => 
                  sig1
              }
              val fm1 = Quantifier(Forall, srt, 
                                   i, 
                                   Atom(R("=",List(Fn(vr1,args),tm))));

              // order matters! we want p to still point to phi
              c1 = c1 ++ List(fm1);

          }
          val sq1 = replace(p, Sequent(sig1, c1, s), phi1)
          Some((List(sq1), Nil))
        case _ =>
          None
      }
   }
 }

 /* This rule lets us work on updates that are are perhaps not at the
  * outermost level of our sequent. This may be useful after an
  * application of qdiffsolve in StandardMode.
  */
  val update = new ProofRule("update") {
    def apply(p: Position) = sq => {
      val Sequent(sig, c, s) = sq
      val fm = lookup(p, sq)
      Prover.extract_update(fm) match {
        case None => None
        case Some((g, Modality(_, AssignQuantified(i, srt, vs), phi))) =>
          var phi1 = phi;
          var sig1 = sig;
          var c1 : List[Formula] = Nil;
          for(v <- vs) v match {
              case (Fn(vr,Nil), tm) if Prover.firstorder(phi1) =>
                phi1 = Prover.extract(Fn(vr, Nil), phi1)(tm)
              case (Fn(vr, args), tm) if Prover.hasFn_Formula(vr, phi) =>
                val vr1 = Prover.uniqify(vr);
                phi1 = Prover.renameFn(vr, vr1, phi1);
                sig1 = sig.get(vr) match {
                  case Some(sg) =>
                    sig1.+((vr1, sg))
                  case _ => 
                    sig1
                }
                val fm1 = Quantifier(Forall, srt,
                                     i,
                                     Atom(R("=", List(Fn(vr1, args), tm))));

                // order matters! we want p to still point to phi
                c1 = c1 ++ List(fm1);

              case _ => ()
          }
          phi1 = AM.list_conj(phi1 :: c1)
          val sq1 = replace(p, Sequent(sig1, c, s), g(phi1))
          Some((List(sq1), Nil))
        case _ => None
      }
    }
  }


  /* this assumes that we don't have any
   *  free variables from existentials */
 val assignAnyRight = new ProofRule("assignanyright") {
    def apply(p: Position) = sq => (p, sq) match {
     case (RightP(n),Sequent(sig, c, s)) => 
      val fm = lookup(p,sq)
      fm match {
        case Modality(Box,AssignAny(Fn(vr, Nil)),phi) =>
          val vr1 = Prover.uniqify(vr)
          val phi1 = Prover.renameFn(vr, vr1, phi)
          val sig1 = sig.get(vr) match {
            case Some(sg ) =>
              sig.+((vr1, sg))
            case _ => 
              sig
          }
          val sq1 = replace(p, Sequent(sig1, c, s), phi1)
          Some((List(sq1), Nil))
        case Modality(Box,AssignAny(f@Fn(vr, List(i))), phi) =>
          val vr1 = Prover.uniqify(vr)
          val vr2 = Prover.uniqify(vr)
          val f1 = Fn(vr1, List(i))
          val phi1 = Prover.renameFn(vr, vr1, phi)
          val (srt1, sig1) = sig.get(vr) match {
            case Some(sg@( List(srt1), rtn)) =>
              (srt1, sig + ((vr1, sg)) + ((vr2, (Nil, rtn))))
            case _ => 
              (AnySort, sig)
          }
          val j = Prover.uniqify("j")
          val asgn = Quantifier(Forall, srt1, j,
                                Binop(Imp, 
                                      Not(Atom(R("=", List(Var(j),i)))),
                                      Atom(R("=",
                                             List(Fn(vr1,List(Var(j))),
                                                  Fn(vr,List(Var(j))))))))
          val asgn0 = Atom(R("=", List(Fn(vr2, Nil),
                                       Fn(vr1, List(i)))))
                                                 
          val Sequent(sig2,s2,c2) = replace(p, Sequent(sig1,c,s), phi1)
          Some((List(Sequent(sig2,asgn0::asgn::s2,c2)),Nil))
        case Modality (Box, 
                       AssignAnyQuantified(i,_,f@Fn(vr,List(Var(j)))), 
                       phi) if j == i =>
          val vr1 = Prover.uniqify(vr)
          val phi1 = Prover.renameFn(vr,vr1,phi)
          val sig1 = sig.get(vr) match {
            case Some(sg ) =>
              sig.+((vr1,sg))
            case _ => 
              sig
          }
          val sq1 = replace(p, Sequent(sig1 ,c,s), phi1)
          Some((List(sq1),Nil))                         
        case _ =>
          None
      }
     case _ => None
   }
 }
   
  //
  // loop rules
  //

  val loopInduction : Formula => ProofRule = 
    inv => new ProofRule("loopInduction[" 
                         + Printing.stringOfFormula(inv) + "]") {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (RightP(n), Sequent(sig, c,s)) =>
          val fm = lookup(pos,sq)
          fm match {
            case Modality(Box,Loop(hp, True, inv_hints), phi) =>
              val initiallyvalid = 
                replace(pos, sq, inv)
              val inductionstep = 
                Sequent(sig, List(inv), List(Modality(Box, hp, inv)))
              val closestep = 
                Sequent(sig, List(inv), List(phi))
              Some((List(initiallyvalid, inductionstep, closestep),
                    Nil))
            case _ => 
              None
          }
        case _ => None
      }
    }

  val iterate = new ProofRule("iterate") {
      def apply(p: Position) = sq => {
	      val fm = lookup(p,sq)
          fm match {
            case Modality(Box,
                          hp1@Loop(hp, True, inv_hints), phi) =>
              val fm1 = Binop(And, phi, 
                              Modality(Box,
                                       Seq(hp, hp1), fm))
              val sq1 = replace(p, sq, fm1)
              Some((List(sq1),Nil))
            case Modality(Diamond,
                          hp1@Loop(hp, True, inv_hints), phi) =>
              val fm1 = Binop(Or, phi, 
                              Modality(Box,
                                       Seq(hp, hp1), fm))
              val sq1 = replace(p, sq, fm1)
              Some((List(sq1),Nil))
            case _ => 
              None
          }
      }
    }

  
  //
  // differential equation rules
  //

  val diffClose = new ProofRule("diffClose") {
    def apply(pos: Position) = sq => (pos,sq) match { 
      case(RightP(n), Sequent(sig, c,s)) =>
        val fm = lookup(pos,sq)
        fm match {
          case Modality(Box,Evolve(derivs,h,_,_), phi) =>
            val closed = Sequent(sig, List(h), List(phi))
            Some((List(closed), Nil))
          case Modality(Box,
                        EvolveQuantified(i, st, derivs, h, _),
                        phi) =>
            val closed = Sequent(sig, 
                                 List(Quantifier(Forall, st, i, h)),
                                 List(phi))
            Some((List(closed), Nil))
          case _ => None
        }
      case _ => None
    }
  }  

  val diffStrengthen : Formula => ProofRule = 
    inv => new ProofRule("diffStrengthen["
                         + Printing.stringOfFormula(inv) + "]") {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (RightP(n), Sequent(sig, c,s)) =>
          println("checking diffstrengthen")
          val fm = lookup(pos,sq)
          fm match {
            case Modality(Box,Evolve(derivs,h,inv_hints,sols), phi) =>
              val (ind_asm, ind_cons) = 
                if(Prover.openSet(inv)) 
                  ( List(inv,h), 
                    Prover.setClosure(Prover.totalDeriv(None, derivs, inv)))
                else ( List(h), Prover.totalDeriv(None, derivs, inv))
              val inv_hints1 = inv_hints.filter( inv != _)
              val fm1 = Modality(Box,
                                 Evolve(derivs, 
                                        Binop(And,h,inv),
                                        inv_hints1, 
                                        sols),
                                 phi) 
              val iv = Sequent(sig, h::c, List(inv))
              val ind = Sequent(sig, ind_asm, List(ind_cons))
              val str = replace(pos,sq, fm1)
              Some((List(iv,ind,str), Nil))
            case Modality(Box,
                          EvolveQuantified(i, st, derivs, h, sols),
                          phi) =>
              val (ind_asm, ind_cons) = 
                (List(Quantifier(Forall, st, i, h)), 
                 Prover.totalDeriv(Some(i), derivs, inv))
              val fm1 = Modality(Box,
                                 EvolveQuantified(i, st,
                                                  derivs, 
                                                  Binop(And,h,inv),
                                                  sols), 
                                 phi) 
              val iv = Sequent(sig, 
                               (Quantifier(Forall, st, i, h))::c, 
                               List(inv))
              val ind = Sequent(sig, ind_asm, List(ind_cons))
              val str = replace(pos, sq, fm1)
              Some((List(iv, ind, str), Nil))

            case _ => None
          }
        case _ => None
      }
    }

  sealed abstract class DiffSolveMode
  case object Standard extends DiffSolveMode
  case object Endpoint extends DiffSolveMode

  val diffSolve : DiffSolveMode => List[Formula] => ProofRule = 
    mode => fm_sols => new ProofRule("diffsolve[" + mode.toString() + "][" 
                          + fm_sols.map(Printing.stringOfFormula) 
                          + "]") {

      import Prover._

      class BadSolution extends Exception 

      def extract(sol: Formula): (String, (Fn, Term)) = sol match {
        case Quantifier(Forall,Real,
                        t, Atom(R("=", 
                                  List(Fn(f,args),
                                       sol_tm)))) if Var(t) == args.head =>
                                         (t,(Fn(f, args.tail),sol_tm))
        case _ => 
          println( sol)
        throw new BadSolution
      }

      def time_var(t_sols: List[(String,(Fn,Term))])
      : Option[String] = {
        val ts = t_sols.map(_._1)
        ts match {
          case Nil => None
          case (t ::rest ) =>
            if( rest.exists(x => x != t)){
              None
            } else {
              Some(t)
            }
        }
      }

      // TODO what if t is a variable in deriv?
      // XXX TODO check inital values
      def is_ok(t: String,
                deriv: (Fn,Term),
                sols: List[(Fn,Term)]  ) : Boolean  = deriv match {
        case (x, tm) =>
          true
           /* XXX TODO . Maybe just make a new subgoal to prove this
          println("testing if ok: " + x + "   " + tm)
          println("t= " + t)
          Prover.assoc(x,sols) match {
            case Some(sol) =>
              val dsol = totalDerivTerm(List((Fn(t,Nil),Num(Exact.one))), sol)
              val tm_sub = Assign(sols,tm)
     
              if(  polynomial_equality(tm_sub, dsol)     ) {
                println("it's ok")
                true
              } else {
                println("it's not ok")
                false
              }
            case None => 
              println("no corresponding solution found in:")
            println(sols)
            false
            
          }
*/
       }

      def apply(pos: Position) = sq => (pos,sq, lookup(pos, sq)) match {
        case (RightP(n), 
              Sequent(sig, c,s),
              Modality(Box,Evolve(derivs, h, _, _ ), phi)) =>
          val t_sols = fm_sols.map(extract)
          val sols0 = t_sols.map(_._2)

          time_var(t_sols) match {
            case None => None
            case Some(t) =>
              val sols = sols0.map(f => (f._1,
                substitute_Term( t,Fn(t,Nil), 
                                   f._2)) )
              val oks = derivs.map(d => is_ok(t, d, sols))
            if(oks.contains(false))
              None
            else {

              val t2 = uniqify(t)
              val t_range = Atom(R(">=", List(Fn(t, Nil), Num(Exact.zero))))
              val t2_range = 
                Binop(And,Atom(R(">=", List(Fn(t2,Nil), Num(Exact.zero)))),
                      Atom(R("<=", List(Fn(t2,Nil), Fn(t,Nil)))))
              val endpoint_h = Modality(Box,Assign(sols), h)
              val interm_h0 =  Modality(Box,Assign(sols),h)
              val interm_h =  renameFn(t,t2,interm_h0)
              val new_xs = sols.map(x  => x._1)//=> Fn(uniqify(x._1.f), Nil))
              val old_and_new_xs = 
                sols.map(_._1).zip(new_xs)
              val new_xs_and_sols = 
                new_xs.zip(sols.map(_._2))
              val assign_hp = 
                Assign(new_xs_and_sols);
              val phi1 = 
                old_and_new_xs.foldRight(phi)( (xs ,phi1) =>
                  renameFn(xs._1.f, xs._2.f, phi1))
              val phi2 = 
                Modality(Box,assign_hp, phi1)
              val stay_in_h = 
                Quantifier(Forall, Real, t2, Binop(Imp,t2_range, interm_h))
              val newgoal = mode match {
                case Standard =>
                  replace(pos,Sequent(sig, stay_in_h ::t_range::c,s), phi2)
                case Endpoint =>
                  replace(pos,Sequent(sig, endpoint_h ::t_range::c,s), phi2)
              }
              Some(List(newgoal), Nil)
            }
          }
          
        case _ => 
          None
      }
                                                        
    }



  val qDiffSolve : DiffSolveMode => List[Formula] => ProofRule = 
    mode => fm_sols => new ProofRule("qDiffsolve[" + mode.toString() + "][" 
                          + fm_sols.map(Printing.stringOfFormula) 
                          + "]") {

      import Prover._

      class BadSolution extends Exception 

      def extract(sol: Formula): (String, (Fn, Term)) = sol match {
        case Quantifier(Forall,Real,
                        t, Atom(R("=", 
                                  List(Fn(f, args),
                                       sol_tm)))) if Var(t) == args.head =>
                                         (t,(Fn(f, args.tail),sol_tm))
        case _ => 
          println( "bad solution:" + sol)
        throw new BadSolution
      }

      def time_var(t_sols: List[(String,(Fn,Term))])
      : Option[String] = {
        val ts = t_sols.map(_._1)
        ts match {
          case Nil => None
          case (t ::rest ) =>
            if( rest.exists(x => x != t)){
              None
            } else {
              Some(t)
            }
        }
      }

      // TODO what if t is a variable in deriv?
      // XXX TODO check inital values
      def is_ok(t: String,
                deriv: (Fn,Term),
                sols: List[(Fn,Term)]  ) : Boolean  = deriv match {
        case (x, tm) =>
          true
           /* XXX TODO . Maybe just make a new subgoal to prove this
          println("testing if ok: " + x + "   " + tm)
          println("t= " + t)
          Prover.assoc(x,sols) match {
            case Some(sol) =>
              val dsol = totalDerivTerm(List((Fn(t,Nil),Num(Exact.one))), sol)
              val tm_sub = Assign(sols,tm)
     
              if(  polynomial_equality(tm_sub, dsol)     ) {
                println("it's ok")
                true
              } else {
                println("it's not ok")
                false
              }
            case None => 
              println("no corresponding solution found in:")
            println(sols)
            false
            
          }
*/
       }

      def apply(pos: Position) = sq => (pos,sq, lookup(pos, sq)) match {
        case (RightP(n), 
              Sequent(sig, c,s),
              Modality(Box,EvolveQuantified(i,srt, derivs, h, _), phi)) =>
          val t_sols = fm_sols.map(extract)
          val sols0 = t_sols.map(_._2)

          time_var(t_sols) match {
            case None => None
            case Some(t) =>
              val sols = sols0.map(f => (f._1,
                substitute_Term( t,Fn(t,Nil), 
                                   f._2)) )
              val oks = derivs.map(d => is_ok(t, d, sols))
            if(oks.contains(false))
              None
            else {

              val t2 = uniqify(t)
              val t_range = Atom(R(">=", List(Fn(t, Nil), Num(Exact.zero))))
              val t2_range = 
                Binop(And,Atom(R(">=", List(Var(t2), Num(Exact.zero)))),
                      Atom(R("<=", List(Var(t2), Fn(t,Nil)))))
              val qh = 
                if(Util.fv(h).contains(i)){
                  Quantifier(Forall, srt, i, h)
                } else {
                  h // cheating so I don't have to deal with such quantifiers for now.
                }
              val assign_hp = AssignQuantified(i,srt,sols)
              val interm_h0 =  Modality(Box,assign_hp,qh)
              val interm_h =  varifyFn(t,t2,interm_h0)
              val phi1 = 
                Modality(Box,assign_hp, phi)
              val endpointphi = Modality(Box,AssignQuantified(i,srt,sols), 
                                         Binop(Imp, qh, phi))

              val stay_in_h = 
                Quantifier(Forall, Real, t2, Binop(Imp,t2_range, interm_h))
              val newgoal = mode match {
                case Standard => 
                  replace(pos,Sequent(sig, stay_in_h ::t_range::c,s), phi1)
                case Endpoint =>
                  replace(pos,Sequent(sig, t_range::c,s), endpointphi)
              }
              Some(List(newgoal), Nil)
            }
          }
          
        case _ => 
          None
      }
                                                        
    }

  //
  // equality substitution rule
  //

  val substitute = new ProofRule("substitute") {
    import Prover._

    def apply(pos: Position) = sq => (pos,sq, lookup(pos, sq)) match {
      case (LeftP(n), Sequent(sig, ctxt,sc), Atom(R("=", List(tm1,tm2))))
        if Util.fv_Term(tm1) == Nil
             &&  (ctxt ++ sc).forall(firstorder) =>
          val ctxt1 = removelist(n, ctxt)
          val ctxt2 = 
            ctxt1.map(x => extract(tm1, x)(tm2))
          val sc1 = sc.map(x => extract(tm1, x)(tm2))
          Some(List(Sequent(sig, ctxt2, sc1)), Nil)
      case _ =>
        None
    }

  }

  //
  // cuts
  //

  val directedCut : Formula => ProofRule = 
    fm => new ProofRule("directedCut["
                         + Printing.stringOfFormula(fm) + "]") 
  {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (LeftP(n), Sequent(sig, c,s)) =>
//          val lem = Sequent(sig, c, fm::s)
          val lem = Sequent(sig, c, List(fm))
          val rep = replace(pos, sq, fm)
          Some(List(lem,rep     ), Nil)
        case  _ => None
        


      }
  }


  /* XXX don't use position */
  val cut : Formula => ProofRule = 
    fm => new ProofRule("cut["
                         + Printing.stringOfFormula(fm) + "]") 
  {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (_, Sequent(sig, c,s)) =>
//          val lem = Sequent(sig, c, fm::s)
          val lem = Sequent(sig, c, List(fm))
          val uselem = Sequent(sig,fm::c,s)
          Some(List(lem,uselem     ), Nil)
        case  _ => None        

      }
  }


  val cutKeepSucc : Formula => ProofRule = 
    fm => new ProofRule("cutKeepSucc["
                         + Printing.stringOfFormula(fm) + "]") 
  {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (_, Sequent(sig, c,s)) =>
          val lem = Sequent(sig, c, fm::s)
          val uselem = Sequent(sig,fm::c,s)
          Some(List(lem,uselem     ), Nil)
        case  _ => None        
      }
  }

  val unsubstitute : Term => ProofRule = 
    tm => new ProofRule("unsubstitute " + tm) {    
    import Prover._

    def apply(pos: Position) = sq => sq match {
      case Sequent(sig, ctxt, sc) 
        if (ctxt ++ sc).forall(firstorder) && 
            Util.fv_Term(tm).length == 0 =>
        val f = tm match {
          case Fn(f_name, _)
            if !List("*", "-", "+", "/", "^").contains(f_name) => uniqify(f_name)
          case _ => uniqify("X")
        }
        val ctxt1 = 
          ctxt.map(x => extract(tm, x)(Fn(f,Nil)))
        val sc1 = 
          sc.map(x => extract(tm, x)(Fn(f,Nil)))
        val fms = ctxt1 ++ sc1
        val f_sort = infersort(sig, tm)
        val sig1 = sig + ((f, (Nil, f_sort)))
        val sq1 = Sequent(sig1, ctxt1, sc1)
        if (ctxt1 == ctxt && sc1 == sc) {
          None
        } else {
          Some((List(sq1), Nil))
        }
      case _ =>
        None
    }
  }

  val prenexify = new ProofRule("prenexify"){
    def apply(pos: Position) = sq => {
      val fm = lookup(pos,sq)
      if (Prover.firstorder(fm)) {
        val fm1 = Util.prenex(fm)
        val sq1 = replace(pos,sq,fm1)
        Some((List(sq1), Nil))
      }else{
        None
      }
    }
  }

  val commutequantifiers = new ProofRule("commutequantifiers"){
    def apply(pos: Position) = sq => lookup(pos,sq) match {
      case Quantifier(qt1,srt1,i1, 
                      Quantifier(qt2,srt2,i2, qfm)) 
      if qt1 == qt2 =>
        val fm1 = Quantifier(qt2,srt2,i2, 
                             Quantifier(qt1,srt1,i1, qfm))
        val sq1 = replace(pos,sq,fm1)
        Some((List(sq1), Nil))
      case _ => None
      
    }
  }

}

