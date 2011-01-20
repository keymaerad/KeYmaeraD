package DLBanyan


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
  

//  type ProofRuleCtxt = Formula => FormulaCtxt => ProofRule

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
          if(sq.scdts.contains(fm) )
            Some((Nil,Nil)) // proved!
          else None
        case (RightP(n), fm) =>
          if(sq.ctxt.contains(fm) )
            Some((List(Sequent(fs,Nil,List(True))),Nil)) // proved!
          else None
      }
    } 
  }


  val hide = new ProofRule("hide") {
    def apply(p:Position) = sq => 
      Some( (List(remove(p,sq)   ), Nil )   )
  }

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
        fm match {
          case Quantifier(Forall, srt, v, phi) =>
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


  val seq = new ProofRule("seq") {
    def apply(p: Position) = sq => {
      val fm  = lookup(p,sq)
      fm match {
        case  Modality(Box,Seq(h1,h2), phi) => 
           val fm1 = Modality(Box,h1,Modality(Box,h2,phi))
           val sq1 = replace(p,sq,fm1)
           Some( List(sq1),Nil)
        case _ => None
      }
    }
  }

  val choose = new ProofRule("choose") {
    def apply(p: Position) = sq =>  {
        val fm = lookup(p,sq)
        fm match {
          case Modality(Box,Choose(h1,h2), phi) => 
            val fm1 = Modality(Box,h1,phi) 
            val fm2 = Modality(Box,h2,phi)
            val sq1 = replace(p,sq,fm1)
            val sq2 = replace(p,sq,fm2)
            Some( (List(sq1,sq2),Nil))
          case _ => 
            None
        }
    }
  }

  val check = new ProofRule("check") {
    def apply(p: Position) = sq =>  {
        val fm = lookup(p,sq)
        fm match {
          case Modality(Box,Check(fm1), phi) => 
            val fm2 = Binop(Imp,fm1, phi)
            val sq1 = replace(p,sq, fm2)
            Some( (List(sq1),Nil))
          case _ => 
            None
        }
    }
  }
 


 val assign = new ProofRule("assign") {
    def apply(p: Position) = sq =>   {
      val Sequent(sig, c,s) = sq
      val fm = lookup(p,sq)
      fm match {
        case Modality(Box,Assign(vs),phi) =>
          var phi1 = phi;
          var sig1 = sig;
          var c1 = c;
          for( v <- vs) {
              val (Fn(vr,Nil), tm) = v;
              val vr1 = Prover.uniqify(vr);
              phi1 = Prover.renameFn(vr,vr1,phi1);
              sig1 = sig.get(vr) match {
                case Some(sg ) =>
                  sig1.+((vr1,sg))
                case _ => 
                  sig1
              }
              val fm1 = Atom(R("=",List(Fn(vr1,Nil),tm)));
              c1 = c1 ++ List(fm1);
                // order matters! we want p to still point to phi
          }
          val sq1 = replace(p, Sequent(sig1,c1,s) , phi1)
          Some((List(sq1),Nil))
        case _ =>
          None
      }
   }
 }


 val qassign = new ProofRule("qassign") {
    def apply(p: Position) = sq =>   {
      val Sequent(sig, c,s) = sq
      val fm = lookup(p,sq)
      fm match {
        case Modality(Box,AssignQuantified(i,srt,vs),phi) => 
          var phi1 = phi;
          var sig1 = sig;
          var c1 = c;
          for( v <- vs) {
              val (Fn(vr,args), tm) = v;
              val vr1 = Prover.uniqify(vr);
              phi1 = Prover.renameFn(vr,vr1,phi1);
              sig1 = sig.get(vr) match {
                case Some(sg ) =>
                  sig1.+((vr1,sg))
                case _ => 
                  sig1
              }
              val fm1 = Quantifier(Forall,srt, 
                                   i, 
                                   Atom(R("=",List(Fn(vr1,args),tm))));
              c1 = c1 ++ List(fm1);
                // order matters! we want p to still point to phi
          }
          val sq1 = replace(p, Sequent(sig1,c1,s) , phi1)
          Some((List(sq1),Nil))
        case _ =>
          None
      }
   }
 }


  /* this assumes that we don't have any
   *  free variables from existentials */
 val assignAnyRight = new ProofRule("assignanyright") {
    def apply(p: Position) = sq => (p,sq) match {
     case (RightP(n),Sequent(sig, c,s)) => 
      val fm = lookup(p,sq)
      fm match {
        case Modality(Box,AssignAny(Fn(vr, Nil)),phi) =>
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
        case Modality(Box,AssignAny(f@Fn(vr, List(i))),phi) =>
          val vr1 = Prover.uniqify(vr)
          val vr2 = Prover.uniqify(vr)
          val f1 = Fn(vr1, List(i))
          val phi1 = Prover.renameFn(vr,vr1,phi)
          val (srt1, sig1) = sig.get(vr) match {
            case Some(sg@( List(srt1), rtn) ) =>
              (srt1, sig + ((vr1,sg)) + ((vr2, (Nil,rtn)))  )
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

        case _ =>
          None
      }
     case _ => None
   }
 }


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


  val diffClose = new ProofRule("diffClose") {
    def apply(pos: Position) = sq => (pos,sq) match { 
      case(RightP(n), Sequent(sig, c,s)) =>
        val fm = lookup(pos,sq)
        fm match {
          case Modality(Box,Evolve(derivs,h,_,_), phi) =>
            val closed = Sequent(sig, List(h), List(phi))
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
                    Prover.setClosure(Prover.totalDeriv(derivs,inv)))
                else ( List(h), Prover.totalDeriv(derivs,inv))
              val inv_hints1 = inv_hints.filter( inv != _)
              val fm1 = Modality(Box,
                                 Evolve(derivs, 
                                        Binop(And,h,inv),
                                        inv_hints1, 
                                        sols), phi) 
              val iv = Sequent(sig, h::c, List(inv))
              val ind = Sequent(sig, ind_asm, List(ind_cons))
              val str = replace(pos,sq, fm1)
              Some((List(iv,ind,str), Nil))

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
              Modality(Box,EvolveQuantified(i,srt, derivs, h), phi)) =>
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
              val endpoint_h = Modality(Box,AssignQuantified(i,srt,sols), h)
              val interm_h0 =  Modality(Box,AssignQuantified(i,srt,sols),h)
              val interm_h =  renameFn(t,t2,interm_h0)
              val new_xs = sols.map(x => x._1) //Fn(uniqify(x._1.f), Nil))
              val old_and_new_xs = 
                sols.map(_._1).zip(new_xs)
              val new_xs_and_sols = 
                new_xs.zip(sols.map(_._2))
              val assign_hp = 
                AssignQuantified(i,srt,new_xs_and_sols);
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



  val substitute = new ProofRule("substitute") {
    import Prover._

    def apply(pos: Position) = sq => (pos,sq, lookup(pos, sq)) match {
      case (LeftP(n), Sequent(sig, ctxt,sc), Atom(R("=", List(Fn(v,Nil),tm)))) 
        if (ctxt ++ sc).forall(firstorder) =>
//          println("applying substitute. tm = " + tm)
          val ctxt1 = removelist(n,ctxt)
          val ctxt2 = 
            ctxt1.map(x => extract(Fn(v,Nil), x)(tm))
          val sc1 = sc.map(x => extract(Fn(v,Nil), x)(tm))
          Some(List(  Sequent(sig, ctxt2,sc1))    ,Nil)
      case _ =>
        None
    }

  }



  val directedCut : Formula => ProofRule = 
    fm => new ProofRule("directedCut["
                         + Printing.stringOfFormula(fm) + "]") 
  {
      def apply(pos: Position) = sq => (pos,sq) match {
        case (LeftP(n), Sequent(sig, c,s)) =>
          val lem = Sequent(sig, c, List(fm))
          val rep = replace(pos, sq, fm)
          Some(List(lem,rep     ), Nil)
        case  _ => None
        


      }
  }

  val nullarize : String => ProofRule = 
    f => new ProofRule("nullarize " + f) {
    
    import Prover._

    def apply(pos: Position) = sq => (pos,sq, lookup(pos, sq)) match {
      case (LeftP(n), Sequent(sig, ctxt,sc), 
            Not(Atom(R("=", List(Fn(i,Nil),Fn(j,Nil))))))
        if (ctxt ++ sc).forall(firstorder) =>
          val fi = uniqify(f)
          val fj = uniqify(f)
          val ctxt1 = 
            ctxt.map(x => extract(Fn(f,List(Fn(i,Nil))), x)(Fn(fi,Nil)))
          val sc1 = 
            sc.map(x => extract(Fn(f,List(Fn(i,Nil))), x)(Fn(fi,Nil)))
          val ctxt2 = 
            ctxt1.map(x => extract(Fn(f,List(Fn(j,Nil))), x)(Fn(fj,Nil)))
          val sc2 = 
            sc1.map(x => extract(Fn(f,List(Fn(j,Nil))), x)(Fn(fj,Nil)))
          val fms = ctxt2 ++ sc2
          val fmsr = fms.map(fm1 => hasFn_Formula(f,fm1))
          val sig1 = sig.get(f) match {
            case Some((args,rtn) ) =>
              sig + ((fi,(Nil,rtn))) + ((fj, (Nil,rtn)))
            case _ => 
              sig
          }
          if(fmsr.exists(x => x))
            None
          else
            Some((List(  Sequent(sig1, ctxt2,sc2))    ,Nil))
      case _ =>
        None
    }

  }

  


}

