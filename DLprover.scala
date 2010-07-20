package DLBanyan
/*
import java.io.BufferedWriter
import java.io.OutputStreamWriter
import java.io.BufferedReader
import java.io.InputStreamReader
*/

import scala.collection.immutable.ListSet
import scala.collection.immutable.HashSet


//import ExactArith._



final object Prover {

//  import BanyanPublic._

  // for fresh variable names
  var uniqid: Int = 0

  
  def uniqify(s: String): String = {
//    val s1 =   s + "$" + getShortName + "$" + uniqid
    val s1 = s + "$" + uniqid
    uniqid = uniqid + 1
    s1
  }
  
  def assoc[A,B](k: A, al: List[(A,B)]): Option[B] = al match {
    case (a,b) :: rest =>
      if( k == a ) Some(b)
      else assoc(k, rest)
    case Nil => None
  }


  def totalDerivTerm(d: List[(String, Term)], tm: Term) : Term = tm match {
    case Var(s) =>  assoc(s,d) match {
      case Some(x) => x
      case None => Num(Exact.Integer(0))
    }
    case Fn("+", List(t1,t2)) =>
      Fn("+", List( totalDerivTerm(d,t1),  totalDerivTerm(d,t2)))
    case Fn("-", List(t1,t2)) =>
      Fn("-", List( totalDerivTerm(d,t1),  totalDerivTerm(d,t2)))
    case Fn("-", List(t1)) =>
      Fn("-", List( totalDerivTerm(d,t1)))
    case Fn("*", List(t1,t2)) =>
      Fn("+", List(Fn("*", List(totalDerivTerm(d,t1),  t2)),
                   Fn("*", List(t1,totalDerivTerm(d,t2)))))
    case Fn("/", List(t1,Num(n))) =>
      Fn("/", List( totalDerivTerm(d,t1), Num(n)))
    case Fn("^", List(t1,Num(n))) =>
      if(n == Exact.Integer(2)) {
        Fn("*", 
           List(Num(n),  
                Fn("*", List(t1,
                             totalDerivTerm(d, t1 )))))
      } else { 
        Fn("*", 
           List(Num(n),  
                Fn("*", List(Fn("^",List(t1,Num(n-Exact.Integer(1)))),
                             totalDerivTerm(d, t1 )))))
      }
    case Fn(f,_) => throw new Error("don't know how to take derivative of " + f)
    case Num(n) => Num(Exact.Integer(0))

  }


  // TODO handle other cases
  def totalDeriv(d: List[(String,Term)], fm: FOFormula) : FOFormula 
    = fm match {
      case True => True
      case False => False
      case Atom(R(r, tms)) =>
        val tms1 = tms.map( (t: Term) =>  totalDerivTerm(d, t ))
        Atom(R(r, tms1))
      //case Not(f) => Not(totalDeriv(d,f))
      case And(f1,f2) => And(totalDeriv(d,f1), totalDeriv(d,f2))

                       // not "Or" here!
      case Or(f1,f2) => And(totalDeriv(d,f1), totalDeriv(d,f2))
      
      //case Imp(f1,f2) => Imp(totalDeriv(d,f1), totalDeriv(d,f2))
      //case Iff(f1,f2) => Iff(totalDeriv(d,f1), totalDeriv(d,f2))
      case _ => 
        throw new Error("can't take total derivative of quantified term " +
                        fm);
                      //P.string_of_FOFormula(fm))

    }

  def varsOfTerm(tm: Term): HashSet[String] = tm match {
    case Var(x)  =>
      HashSet.empty + x
    case Fn(f, ps) =>
      ps.map(varsOfTerm).foldRight(HashSet[String]())((x,y) => x ++ y)
    case _ => HashSet.empty

  }


  def polynomial_equality(pol1: Term, pol2: Term): Boolean = {
    val vars = varsOfTerm(pol1).toList
    val cpol = AM.tsimplify(AM.polynate(vars, Fn("-", List(pol1,pol2))))
    cpol match {
      case Num(x) if x.is_zero => true
      case _ => false
    }
    
  }

  // conservative guess as to whether this formula is an open set
  def openSet(fm: FOFormula): Boolean = fm match {
    case Atom(R("<", _)) => true
    case Atom(R(">", _)) => true
    case And(fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case Or(fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case _ => false
  }

  def setClosure(fm: FOFormula): FOFormula = fm match {
    case Atom(R("<", ts)) => Atom(R("<=", ts))
    case Atom(R(">", ts)) => Atom(R(">=", ts))
    case And(fm1,fm2)  => And(setClosure(fm1), setClosure(fm2))
    case Or(fm1,fm2)  => Or(setClosure(fm1),setClosure(fm2))
    case _ => throw new Error("unsupported setClosure")
  }


// alpha-renaming
  def rename_Term(xold: String,
                 xnew: String,
                 tm: Term): Term = tm match {
    case Var(x) if x == xold =>
      Var(xnew)
    case Fn(f, ps) =>
      val fnew = if(f == xold) xnew else f
      Fn(fnew, ps.map(p => rename_Term(xold, xnew,p)))
    case _ => tm
  }

  def rename_FOFormula(xold: String,
                      xnew: String,
                      fm: FOFormula): FOFormula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => rename_Term(xold,xnew,p))))
    case Not(f) => Not(rename_FOFormula(xold,xnew,f))
    case And(f1,f2) => 
      And(rename_FOFormula(xold,xnew,f1),rename_FOFormula(xold,xnew,f2))
    case Or(f1,f2) => 
      Or(rename_FOFormula(xold,xnew,f1),rename_FOFormula(xold,xnew,f2))
    case Imp(f1,f2) => 
      Imp(rename_FOFormula(xold,xnew,f1),rename_FOFormula(xold,xnew,f2))
    case Iff(f1,f2) => 
      Iff(rename_FOFormula(xold,xnew,f1),rename_FOFormula(xold,xnew,f2))
    case Exists(v,f) if v != xold =>
      Exists(v, rename_FOFormula(xold,xnew,f))
    case Forall(v,f) if v != xold =>
      Forall(v, rename_FOFormula(xold,xnew,f))
    case _ => fm
  }

  def rename_HP(xold:String,xnew:String,hp:HP):HP = hp match {
    case Assign(x, t) =>
      val x1 = if(x == xold) xnew else x
      val t1 = rename_Term(xold,xnew,t)
      Assign(x1,t1)
    case AssignAny(x) =>
      val x1 = if(x == xold) xnew else x
      AssignAny(x1)
    case Check(fm) =>
      Check(rename_FOFormula(xold,xnew,fm))
    case Seq(p,q) => 
      Seq(rename_HP(xold,xnew,p), rename_HP(xold,xnew,q))
    case Choose(p1,p2) => 
      Choose(rename_HP(xold,xnew,p1), rename_HP(xold,xnew,p2))
    case Repeat(p,fm, inv_hints) =>
      Repeat(rename_HP(xold,xnew,p), 
             rename_FOFormula(xold,xnew,fm), 
             inv_hints.map(f => rename_FOFormula(xold,xnew,f)))
    case Evolve(derivs, fm, inv_hints, sols) =>
      val replace_deriv: ((String, Term)) => (String, Term) = vt => {
        val (v,t) = vt
        val v1 =  if(v == xold) xnew else v
        val t1 = rename_Term(xold,xnew,t)
        (v1,t1)
      }
      Evolve(derivs.map( replace_deriv), 
             rename_FOFormula(xold,xnew,fm),
             inv_hints.map(f => rename_FOFormula(xold,xnew,f)),
             sols.map(f => rename_FOFormula(xold,xnew,f)))
      
  }

  def rename_DLFormula(xold: String, 
                      xnew: String, 
                      dlfm: DLFormula): DLFormula = dlfm match {
    case NoModality(fm) =>
      NoModality(rename_FOFormula(xold, xnew, fm))
    case Box(hp, dlfm1) => 
      val hp1 = rename_HP(xold,xnew,hp)
      Box(hp1, rename_DLFormula(xold,xnew,dlfm1))
  }


  def matchAndSplice[A](lst: List[A],
                        f : A => Option[List[A]]): Option[List[A]]
     = lst match {
       case Nil =>
         None
       case e::es =>
         f(e) match {
           case Some(e1) =>
             Some(e1 ++ es)
           case None => matchAndSplice(es,f) match {
             case None => None
             case Some(es1) => Some(e::es1)
           }
         }
     }


// substitution


  def substitute_Term(xold: String,
                 xnew: Term,
                 tm: Term): Term = tm match {
    case Var(x) if x == xold =>
      xnew
    case Fn(f, ps) =>
      Fn(f, ps.map(p => substitute_Term(xold, xnew, p)))
    case _ => tm
  }


  def simul_substitute_Term(subs: List[(String,Term)],
                            tm: Term): Term = tm match {
    case Var(x) =>
      assoc(x,subs) match {
        case Some(xnew) =>
          xnew
        case None => Var(x)
      }
    case Fn(f, ps) =>
      Fn(f, ps.map(p => simul_substitute_Term(subs, p)))
    case _ => tm
  }


  

  def substitute_FOFormula(xold: String,
                      xnew: Term,
                      xnew_fv: Set[String],
                      fm: FOFormula): FOFormula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => substitute_Term(xold,xnew,p))))
    case Not(f) => Not(substitute_FOFormula(xold,xnew,xnew_fv,f))
    case And(f1,f2) => 
      And(substitute_FOFormula(xold,xnew,xnew_fv,f1),
          substitute_FOFormula(xold,xnew,xnew_fv,f2))
    case Or(f1,f2) => 
      Or(substitute_FOFormula(xold,xnew,xnew_fv,f1),
          substitute_FOFormula(xold,xnew,xnew_fv,f2))
    case Imp(f1,f2) => 
      Imp(substitute_FOFormula(xold,xnew,xnew_fv,f1),
          substitute_FOFormula(xold,xnew,xnew_fv,f2))
    case Iff(f1,f2) => 
      Iff(substitute_FOFormula(xold,xnew,xnew_fv,f1),
          substitute_FOFormula(xold,xnew,xnew_fv,f2))
    case Exists(v,f) =>
      if( ! xnew_fv.contains(v)){
        Exists(v, substitute_FOFormula(xold,xnew, xnew_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_FOFormula(v,v1,f)
        Exists(v1,substitute_FOFormula(xold,xnew, xnew_fv, f1))
      }
    case Forall(v,f) =>
      if( ! xnew_fv.contains(v)){
        Forall(v, substitute_FOFormula(xold,xnew, xnew_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_FOFormula(v,v1,f)
        Forall(v1,substitute_FOFormula(xold,xnew, xnew_fv, f1))
      }
  }


  def simul_substitute_FOFormula1(
                      subs: List[(String,Term)],
                      new_fv: Set[String],
                      fm: FOFormula): FOFormula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => simul_substitute_Term(subs,p))))
    case Not(f) => 
      Not(simul_substitute_FOFormula1(subs,new_fv,f))
    case And(f1,f2) => 
      And(simul_substitute_FOFormula1(subs,new_fv,f1),
          simul_substitute_FOFormula1(subs,new_fv,f2))
    case Or(f1,f2) => 
      Or(simul_substitute_FOFormula1(subs,new_fv,f1),
          simul_substitute_FOFormula1(subs,new_fv,f2))
    case Imp(f1,f2) => 
      Imp(simul_substitute_FOFormula1(subs,new_fv,f1),
          simul_substitute_FOFormula1(subs,new_fv,f2))
    case Iff(f1,f2) => 
      Iff(simul_substitute_FOFormula1(subs,new_fv,f1),
          simul_substitute_FOFormula1(subs,new_fv,f2))
    case Exists(v,f) =>
      if( ! new_fv.contains(v)){
        Exists(v, simul_substitute_FOFormula1(subs, new_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_FOFormula(v,v1,f)
        Exists(v1,simul_substitute_FOFormula1(subs, new_fv, f1))
      }
    case Forall(v,f) =>
      if( ! new_fv.contains(v)){
        Exists(v, simul_substitute_FOFormula1(subs, new_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_FOFormula(v,v1,f)
        Forall(v1,simul_substitute_FOFormula1(subs, new_fv, f1))
      }
  }

  def simul_substitute_FOFormula(                      
                      subs: List[(String,Term)],
                      fm: FOFormula): FOFormula =  {
    val ts = subs.map(_._2)
    val vs = HashSet.empty ++ (ts.map(varsOfTerm).flatten[String])
    simul_substitute_FOFormula1(subs, vs, fm)
  }

}


/*
abstract class SearchStrategy
case class BreadthFirst() extends SearchStrategy
case class DepthFirst() extends SearchStrategy



abstract class ProofRule() {
  def applyRule(succ: Sequent): List[TreeNode]
}


object PRArithmeticFV extends ProofRule{
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fo) ) => 
      val fm = Imp(AM.list_conj(ctxt), fo);
      val c1 = new ArithmeticNode(fm)
      List(c1)
    case _ => 
      Nil
  }
}

object PRArithmetic extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fo) ) => 
      val fm = Imp(AM.list_conj(ctxt), fo);
      val fm1 = AM.univ_close(fm);
      val c2 = new ArithmeticNode(fm1)
      List(c2)
    case _ => 
      Nil
  }
}

object PRRedlog extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fo) ) => 
      val fm = Imp(AM.list_conj(ctxt.reverse), fo);
      val fm1 = AM.univ_close(fm);
      val c2 = new RedlogNode(fm1)
      List(c2)
    case _ => 
      Nil
  }
}


object PRMathematica extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fo) ) => 
      val fm = Imp(AM.list_conj(ctxt.reverse), fo);
      val fm1 = AM.univ_close(fm);
      val c2 = new MathematicaNode(fm1)
      List(c2)
    case _ => 
      Nil
  }
}



    
object PRAssign extends ProofRule{
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Assign(vr, tm), fm)) => 
      val vr1 = Prover.uniqify(vr)
      val fm1 = Prover.rename_DLFormula(vr,vr1,fm)
      val c = new AndNode(
                           "assign", 
                           sq,
                           DepthFirst(),                           
                           List(Sequent( Atom(R("=", 
                                                List(Var(vr1), 
                                                     tm) ))::ctxt, fm1)))
      List(c)
    case _ => Nil
  }
}

object PRAssignAny extends ProofRule{
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(AssignAny(vr), fm)) => 
      val vr1 = Prover.uniqify(vr)
      val fm1 = Prover.rename_DLFormula(vr,vr1,fm)
      val c = new AndNode(
                           "assignany", 
                           sq,
                           DepthFirst(),                           
                           List(Sequent( ctxt, fm1)))
      List(c)
    case _ => Nil
  }
}



object PRCond extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Check(h), fm)) =>
      val c  = new AndNode("cond",
                           sq,
                           DepthFirst(),
                           List(Sequent( h::ctxt, fm)))
      List(c)
    case _ => Nil
  }
}

object PRSeq extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Seq(p1, p2), fm)) => 
      val c  = new AndNode(
                           "seq",
                           sq,
                           DepthFirst(),
                           List(Sequent(ctxt, Box(p1, Box(p2, fm)))))
      List(c)
    case _ => Nil
  }
}
      

object PRChoose extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Choose(p1,p2), fm)) => 
      val c  = new AndNode(
                           "choose",
                           sq,
                           BreadthFirst(),
	                   List(Sequent(ctxt, Box(p1,fm)),
                                Sequent(ctxt, Box(p2,fm))))
      List(c)
    case _ => Nil
  }
}

object PRLoopClose extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Repeat(p1, h, inv_hints), fm)) => 
      val pp = new AndNode("loop-close", 
                           sq,
                           BreadthFirst(),
                           List(Sequent(List(h), fm)))
      List(pp)
    case _ => Nil
  }
}


object PRLoopStrengthen extends ProofRule {
  
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Repeat(p1, h, inv_hints), fm)) => 
      val loop_strengthen: FOFormula => AndNode = inv =>
        new AndNode(
                    "loop strengthening", 
                    sq,
                    DepthFirst(),	
                    List(Sequent(h::ctxt, NoModality(inv)),
                         Sequent(inv::h::Nil, 
                                 Box(p1, NoModality(Imp(h,inv)))),
                         Sequent(ctxt, 
                                 Box(Repeat(p1, 
                                            And(h,inv),
                                            inv_hints - inv),fm))))
      inv_hints.map(loop_strengthen)
    case _ => Nil
  }
}

object PRLoopInduction extends ProofRule {
  
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Repeat(p1, True(), inv_hints), fm)) => 
      val loop_rule: FOFormula => AndNode = inv =>
        new AndNode(
                    "loop induction", 
                    sq,
                    BreadthFirst(),	
                    List(Sequent(ctxt, NoModality(inv)),
                         Sequent(List(inv), 
                                 Box(p1, NoModality(inv))),
                         Sequent(List(inv), 
                                 fm)))
      inv_hints.map(loop_rule)
    case _ => Nil
  }
}



object PRDiffClose extends ProofRule{
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Evolve(derivs, h, inv_hints, sols), fm)) => 
      val pp = new AndNode(
                           "diffclose",
                           sq,
                           DepthFirst(),
                           List(  Sequent(List(h), fm)))
      List(pp)
    case _ => Nil
  }
}


object PRDiffStrengthen extends ProofRule {
  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, Box(Evolve(derivs, h, inv_hints,_), fm)) => 
      val diff_strengthen: FOFormula => AndNode = inv => {
        val (ind_asm,ind_cons) = 
          { if(Prover.openSet(inv)) 
              ( List(inv,h), Prover.setClosure(Prover.totalDeriv(derivs,inv)))
           else
              ( List(h), Prover.totalDeriv(derivs,inv))
         }
        new AndNode(
                    "differential strengthening", 
                    sq,
                    DepthFirst(),
                    List(Sequent(h::ctxt, NoModality(inv)),
                         Sequent(ind_asm, 
                                 NoModality(ind_cons)),
                         Sequent(ctxt, 
                                 Box(Evolve(derivs, 
                                            And(h,inv),
                                            inv_hints - inv,
                                            Nil),fm))))
      }
      inv_hints.map(diff_strengthen)
    case _ => Nil 
  }
}


object PRDiffSolve extends ProofRule {

  import Prover._

  class BadSolution extends Exception 

  def extract(sol: FOFormula): (String, (String, Term)) = sol match {
    case Forall(t, Atom(R("=", List(Fn(f, List(t1)),
                                    sol_tm)))) if Var(t) == t1 =>
       (t,(f,sol_tm))
    case _ => 
      println( sol)
      throw new BadSolution
  }

  def time_var(t_sols: List[(String,(String,Term))])
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
// TODO check inital values
  def is_ok(t: String,
            deriv: (String,Term),
            sols: List[(String,Term)]  ) : Boolean  = deriv match {
   case (x, tm) =>
     println("testing if ok: " + x + "   " + tm)
     println("t= " + t)
     Prover.assoc(x,sols) match {
       case Some(sol) =>
         println("sol= " + P.string_of_Term(sol))
         val dsol = totalDerivTerm(List((t,Num(ExactInt(1)))), sol)
         val tm_sub = simul_substitute_Term(sols, tm)
     
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
  }


  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, 
                 Box(Evolve(derivs, h, invs, fm_sols), phi)) =>
     val t_sols = fm_sols.map(extract)
     val sols = t_sols.map(_._2)
     time_var(t_sols) match {
       case None => Nil
       case Some(t) =>
         val oks = derivs.map(d => is_ok(t, d, sols))
         if(oks.contains(false))
           Nil
         else {
//           val t1 = uniqify(t)
           val t2 = uniqify(t)
//           val t1_range = Atom(R(">=", List(Var(t1), Num(ExactInt(0)))))
           val t_range = Atom(R(">=", List(Var(t), Num(ExactInt(0)))))
           val t2_range = 
             And(Atom(R(">=", List(Var(t2), Num(ExactInt(0))))),
                 Atom(R("<=", List(Var(t2), Var(t)))))
           val endpoint_h = simul_substitute_FOFormula(sols, h)
           val interm_h = 
             rename_FOFormula(t,t2,simul_substitute_FOFormula(sols, h))
           val new_xs = sols.map(x => uniqify(x._1))
           val old_and_new_xs = 
             sols.map(_._1).zip(new_xs)
           val new_xs_and_sols = 
             new_xs.zip(sols.map(_._2))
           val assign_sols = 
             new_xs_and_sols.map(xtm => Assign(xtm._1,xtm._2))
           val phi1 = 
             old_and_new_xs.foldRight(phi)( (xs ,phi1) =>
                                rename_DLFormula(xs._1, xs._2, phi1))
           val assign_hp = 
             assign_sols.foldRight(Check(True()):HP)((x,y) => Seq(x,y))
           val phi2 = 
             Box(assign_hp, phi1)
           val stay_in_h = 
             Forall(t2, Imp(t2_range, interm_h))
           List(
            new AndNode(
                    "solve differential equation", 
                    sq,
                    DepthFirst(),
                    List(Sequent(stay_in_h ::t_range::ctxt, 
                                 phi2))),
            new AndNode(
                    "solve differential equation, endpoint", 
                    sq,
                    DepthFirst(),
                    List(Sequent(endpoint_h ::t_range::ctxt, 
                                 phi2))))
         }
     }

    case _ => Nil 
  }
}


object PRSubstitute extends ProofRule {

  import Prover._
/*
  def isAssign(fm: FOFormula):Option[(String,Term)] = fm match {
    case Atom(R("=", List(Var(v), tm))) => Some(v,tm)
    case _ => None
  }
*/

  def findAssignment(ctxt: List[FOFormula])
       : Option[(String, Term, List[FOFormula])]  = ctxt match {
         case Nil => None
         case Atom(R("=", List(Var(v), tm))) :: rest =>
           Some((v,tm,rest))
         case fm::fms =>
           findAssignment(fms) match {
             case None => None
             case Some((v,tm,rest)) =>
               Some((v,tm,fm::rest))
           }
       }
                     



  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fo) ) => 
      val a = findAssignment(ctxt)
      a match {
        case None => Nil
        case Some((v,tm,ctxt1)) =>
          val tm_vars = varsOfTerm(tm)
          val ctxt2 = 
            ctxt1.map(x => substitute_FOFormula(v, tm, tm_vars, x))
          val fo2 = substitute_FOFormula(v,tm,tm_vars, fo)
          List(new OrNode(Sequent(ctxt2,NoModality(fo2))))
      }
    case _ => Nil
  }

}


object PRAlpha extends ProofRule {
  
  import Prover._

  def matcher(fm: FOFormula): Option[List[FOFormula]] = fm match {
    case And(fm1, fm2) => Some(List(fm1,fm2))
    case True() => Some(Nil)
    case _ => None
  }


  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(Imp(fm1,fm2))) =>
      val ctxt2 = fm1 :: ctxt
      List(new OrNode(Sequent(ctxt2, NoModality(fm2))))
    case Sequent(ctxt, phi) =>
      matchAndSplice(ctxt, matcher) match {
        case None => Nil
        case Some(ctxt1) =>
          List(new OrNode(Sequent(ctxt1,phi)))
      }
  }
}


object PRBeta extends ProofRule {
  

  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(And(fm1,fm2))) =>
      List(new AndNode(
                  "Beta ",
                  sq,
                  BreadthFirst(),
              List(Sequent(ctxt, NoModality(fm1)),
                   Sequent(ctxt, NoModality(fm2)))))
    case _ => Nil
  }
}



// untested
object PRAllLeft extends ProofRule {
  
  import Prover._

  def matcher(v1: String)(fm: FOFormula): Option[List[FOFormula]] = fm match {
    case Forall(v, fm) => 
      Some(List(simul_substitute_FOFormula(List((v,Var(v1))), fm)))
    case _ => None
  }

  def applyRule(sq: Sequent): List[TreeNode] = sq match {
    case Sequent(ctxt, NoModality(fm)) =>
      val fvs = (AM.fv(fm) :: ctxt.map(AM.fv)).flatten[String].removeDuplicates
      fvs.map(x => matchAndSplice(ctxt, matcher(x)) match {
                    case None => Nil
                    case Some(ctxt1) =>
                      List(new OrNode(Sequent(ctxt1, NoModality(fm))))
                  }).flatten[TreeNode]
  
  }


}


*/

/*
@serializable
abstract class DLNode() extends TreeNode() {

  override def mainBranch() : Boolean = checkStatus() match {
    case Returned() =>
        checkReturnValue() match {
          case Some(Proved(rl)) => 
               true
          case _ => false
        }
    case _ => false
  }

  override def colorMain() : String = checkStatus() match {
    case Working() =>
      "white"
    case Returned() =>
        checkReturnValue() match {
          case Some(Proved(rl)) => 
               "blue"
          case Some(Disproved()) => "red"
          case Some(GaveUp()) => 
               "burlywood"
          case _ => "yellow"
        }

    case Irrelevant() =>
      "gray80"
  }

  override def color() : String = checkStatus() match {
    case Working() =>
      "white"
    case Returned() =>
        checkReturnValue() match {
          case Some(Proved(rl)) => 
              "cornflowerblue"
          case Some(Disproved()) => "red"
          case Some(GaveUp()) => 
              "coral"
          case _ => "yellow"
        }
  
    case Irrelevant() =>
      "gray90"
  }
}



@serializable
class ArithmeticNode(fm: FOFormula)
  extends DLNode() {

  def workHere(timeslice: Long): Unit = checkStatus() match {
    case Working() => 
       println("about to attempt quantifier elimination on:\n")
       P.print_FOFormula(fm)
       println("\nredlog version of formula = ")
       println(P.redlog_of_formula(fm))
       println("tickets = " + checkTickets())
       println()
       try{ 
         CV.start()
//         val r =  AM.real_elim_goal(fm)
         val r = AM.real_elim(fm)
         if(r == True()) {
           println("success!")
           returnNode(Proved("quantifer elimination"))
         } else {
           // TODO this doesn't actually mean disproved
           println("failure!")
           println("returned: " + P.string_of_FOFormula(r))
       	   returnNode(GaveUp())
         }      
       } catch {
         case e: CHAbort => 
           println("aborted quantifier elimination")
       }
    case _ =>
      transferTickets(Parent(), checkTickets())          
  }


  def timeout(): Unit = {
    CV.stop()
    timeSlicesToUse *= 2
  }

  def abort(): Unit = {
    CV.stop()
  }

  def handleMessage(msg: Any): Unit = {
    ()
  }
    
  def childReturned(c: Int, v: Any) = {
    // no children
    ()
  }


  override def toString(): String = {
    "ArithmeticNode( " + P.string_of_FOFormula(fm)+ ")"
  } 

}


@serializable
class RedlogNode(fm: FOFormula)
  extends DLNode() {


  var mbe_process: Option[Process] = None

  val processLock = new Lock()


  def workHere(timeSlice: Long): Unit = checkStatus() match {
    case Working() => 
       println("about to attempt quantifier elimination on:\n")
       P.print_FOFormula(fm)
       val rfm = P.redlog_of_formula(fm)
       println("\nredlog version of formula = ")
       println(rfm)
       println("tickets = " + checkTickets())
       println()
       try{ 
         val pb = new ProcessBuilder()
         val mp = pb.environment()
//         val reduce_bin = mp.get("REDUCE_HOME") + "/bin/reduce"
         val reduce_bin = mp.get("REDUCE")
         println("reduce_bin = " + reduce_bin)

         pb.command(reduce_bin)

         
         val process =  pb.start()
         
         processLock.synchronized{ mbe_process = Some(process)} 

         val  out = new BufferedWriter(new OutputStreamWriter(
					process.getOutputStream()))

         println("opened writer")

         out.write("load redlog; off rlverbose; off nat; rlset R;")
         //    out.write("out \"" + tmp.getAbsolutePath() + "\";")
         out.write(" phi:= " + rfm + ";")
         out.write(" \"START\";\n")
         out.write("rlqe phi;\n")
         //    out.write("shut \"" + tmp.getAbsolutePath() + "\";")
         out.write(" \"END\";\n")
         out.write("quit;\n")
         out.flush()

         println("sent input to reduce")

         val exitValue = process.waitFor()
         println("done waiting")


         if (exitValue == 0) {
           val ap = new RedlogParser(process.getInputStream())

           processLock.synchronized{mbe_process = None}

           val r = ap.result
           if(r == True()) {
             println("success!")
             returnNode(Proved("quantifer elimination"))
           } else {
             // TODO this doesn't actually mean disproved
             println("failure!")
             println("returned: " + P.string_of_FOFormula(r))
       	     returnNode(GaveUp())
           }
          } else {println("exit value = " + exitValue)}
       } catch {
         case e => 
           println("aborted quantifier elimination")
         println(e)
       }
    case _ =>
      transferTickets(Parent(), checkTickets())          
  }


  def timeout(): Unit = processLock.synchronized {
    mbe_process match {
      case Some(p) =>
        p.destroy()
        timeSlicesToUse *= 2
        mbe_process = None
      case None =>
      
    }
  }

  def abort(): Unit = processLock.synchronized {
    mbe_process match {
      case Some(p) =>
        p.destroy()
        mbe_process = None
      case None =>
    }
  }

  def handleMessage(msg: Any): Unit = {
    ()
  }
    
  def childReturned(c: Int, v: Any) = {
    // no children
    ()
  }


  override def toString(): String = {
    "RedlogNode( " + P.string_of_FOFormula(fm)+ ")"
  } 

}


object Mathematica {
  import com.wolfram.jlink._



    val mathkernel = 
      {
        val mk = System.getenv("MATHKERNEL")
        if (mk == null) 
          {throw new Error("please set the MATHKERNEL variable")}
        else mk
      }
         
    val linkCall = 
      "-linkmode launch -linkname '" + 
      mathkernel +
      " -mathlink'"



  var mbe_link: Option[KernelLink] = None

  val linkLock = new Lock()



  val messageBlackList = 
    List( ("Reduce", "nsmet"), ( "FindInstance", "nsmet" ),
         ("Reduce", "ratnz"))

  val  mBlist =
    new Expr(new Expr(Expr.SYMBOL,"List"),  
             messageBlackList.map(
               x => new Expr(new Expr(Expr.SYMBOL, "MessageName"),
		                 List( new Expr(Expr.SYMBOL, x._1),
			              new Expr(x._2)).toArray)).toArray)


  def createLink: KernelLink = mbe_link match {
    case None =>
      println("linkCall = " + linkCall)
      println("creating mathlink. ")
      val link = try {
        MathLinkFactory.createKernelLink(linkCall);
      } catch {
        case e => 
          println("could not created kernel link")
        throw e
      }
      println("created.")
      println("error code = " + link.error()) 
    
      link.connect
      link.discardAnswer
      linkLock.synchronized{
        mbe_link = Some(link)
      }


      link
    case Some(link) =>
       link
  }



}



@serializable
class MathematicaNode(fm: FOFormula)
  extends DLNode() {

    import com.wolfram.jlink._
    import Mathematica._


  var eval = false
  val evalLock = new Lock()

  var aborted = false
  val abortLock = new Lock()



  def workHere(timeSlice: Long): Unit = checkStatus() match {
    case Working() if timeSlice > 10 => 
       println(nodeID)
       println("about to attempt quantifier elimination on:\n")
       P.print_FOFormula(fm)
       println()
       println("timeSlice = " + timeSlice)
       System.out.flush
       val mfm = P.mathematica_of_formula(fm)
       val mfm_red = 
         new Expr(new Expr(Expr.SYMBOL, "Reduce"),
                  List(mfm, 
                       new Expr(Expr.SYMBOL, "Reals")).toArray)

       val mfm_tmt = 
         new Expr(new Expr(Expr.SYMBOL, "TimeConstrained"),
                  List(mfm_red, 
                       new Expr(Expr.REAL, 
                                (timeSlice / 1000.0).toString)).toArray)

       val check = new Expr(new Expr(Expr.SYMBOL, "Check"), 
                            List(mfm_red, 
                                 new Expr("$Exception"), 
                                 mBlist ).toArray)


       println("\nmathematica version of formula = ")
       println(mfm_tmt)
       println("tickets = " + checkTickets())
       println()

    
       
       val link = linkLock.synchronized{
                   mbe_link match {
                     case None =>
                       createLink
                     case Some(link1) =>
                       link1
                   }
       }

       try{ 



           link.newPacket()

           println("evaluating expression")

           link.evaluate(mfm_tmt)

         
           var early_abort = false

           println("error code = " + link.error())
           evalLock.synchronized{
             eval = true
             aborted = false
           }
           link.waitForAnswer()
           evalLock.synchronized{
             eval = false
             if(aborted == true ){
               early_abort = true
             }
           }

           println("answer ready")
           println("error code = " + link.error())


         val abortExpr = new Expr(Expr.SYMBOL, "$Aborted")

          val result = link.getExpr();

           evalLock.synchronized{
             if(aborted == true && result != abortExpr ){
               link.newPacket()
               link.evaluate("0")
               link.discardAnswer()
             }
           }


          link.newPacket()

          println("result = " + result)

         if(result == abortExpr) {
           timeSlicesToUse *= 2
           println("doubling timeSlicesToUse")
           //link.discardAnswer()
         } else
         if(result == new Expr(Expr.SYMBOL, "True"))
           {
             println("success!")
             
             println("error code = " + link.error())

             returnNode(Proved("quantifier elimination"))
           } else {
             // TODO this doesn't actually mean disproved
             println("failure!")
             println("returned: " + result)
             println("error code = " + link.error())
       	     returnNode(GaveUp())
           }


       } catch {
         case e:MathLinkException if e.getErrCode() == 11 => 

	     // error code 11 indicates that the mathkernel has died

               println("caught code 11")
       }
    case Working()  => // timeSlice is too small
      timeSlicesToUse *= 2
    case _ =>
      transferTickets(Parent(), checkTickets())          
  }


  def timeout(): Unit = linkLock.synchronized {
    mbe_link match {
      case Some(lnk) =>
/*
        println("about to signal a timeout. " + nodeID)
        System.out.flush
        lnk.abortEvaluation()
        timeSlicesToUse *= 2
        mbe_link = None
        */ 
      case None =>
      
    }
  }

  def abort(): Unit = linkLock.synchronized {

    mbe_link match {
      case Some(lnk) =>
        evalLock.synchronized{
          if (eval == true) {
            println("about to signal an abort. " + nodeID)
            System.out.flush
            lnk.abortEvaluation()

            aborted = true
          }
        }

      case None =>
    }      
  }
    

/*
  override def finalize(): Unit = linkLock.synchronized {
    println("finalizing")
    System.out.flush()
    mbe_link match {
      case Some(lnk) =>
        println("about to signal a finalize. " + nodeID)
        System.out.flush

        lnk.close
        mbe_link = None
      case None =>
        println("nothing to signal")
    }
  }
*/

  def handleMessage(msg: Any): Unit = {
    ()
  }
    
  def childReturned(c: Int, v: Any) = {
    // no children
    ()
  }


  override def toString(): String = {
    "MathematicaNode( " + P.string_of_FOFormula(fm)+ ")"
  } 

}



@serializable
class OrNode(goal: Sequent)
  extends DLNode() {


  val proofRules: List[ProofRule] = 
    List(PRSeq, PRChoose, PRAssign, PRAssignAny,
         PRCond,
//         PRLoopClose, PRLoopStrengthen, 
         PRLoopInduction,
         PRDiffClose, PRDiffStrengthen, PRDiffSolve)



  val arithRules: List[ProofRule] = 
//    List(PRArithmeticFV, PRArithmetic)
//    List(PRRedlog)
    List(PRMathematica)

 




  def initializeChildren(): Unit = {

   // first check to see if we can close
    goal match {
     case Sequent(ctxt, NoModality(fm)) if ctxt.contains(fm) =>
       returnNode(Proved("close "))
       return ()
     case _ => ()
   } 

    val alphaKid = PRAlpha.applyRule(goal)
    alphaKid match {
      case List(k) =>
        newChild(k)
        transferTickets(Child(0), checkTickets)
      case k::ks =>
        throw new Error("alpha returned multiple children")
      case Nil =>
        val kids = proofRules.map( x => x.applyRule(goal)).flatten[TreeNode]
        if(kids.length > 0){ 
          for(k <- kids){
            newChild(k)
          }
          val portion = checkTickets / numChildren
          for(i <- 0 until numChildren() ) {
            transferTickets(Child(i), portion+1)
          }
        } else {
          val betaKid = PRBeta.applyRule(goal)
          betaKid match {
            case List(k) =>
              newChild(k)  
              transferTickets(Child(0), checkTickets)
            case k::ks =>
              throw new Error("beta returned multiple children")
            case Nil => // only arithmetic left
             val kids1 = PRSubstitute.applyRule(goal)
             kids1   match{
              case Nil =>
               val kids = 
                 arithRules.map( x => x.applyRule(goal)).flatten[TreeNode]
//               val kids2 = PRAllLeft.applyRule(goal)
               
               for(k <- (kids  )){
                 newChild(k)
               } 
               if(numChildren > 0){
                 val portion = checkTickets / numChildren
                 for(i <- 0 until numChildren() ) {
                  transferTickets(Child(i), portion+1)
                 }
               }
             case List(k) =>
               newChild(k)
               transferTickets(Child(0), checkTickets)
              case _ =>
               throw new Error("substitution returned multiple goals")
          }
         }
      

        }

    }
  }
 
  var workedHereYet = false
    

  def workHere(timeSlice: Long): Unit = 
    statusLock.synchronized{
      checkStatus() match {
        case Working() if !workedHereYet => 
          initializeChildren()
          workedHereYet = true
          ()
        case Working() if workedHereYet =>
          var giveup = true
          val numActiveKids = 
            childrenStatus.filter(x => x.get match 
                                  { case Working() => true
                                   case _ => false }).length 
          for( i <- childrenStatus.indices.reverse) 
            childrenStatus(i).get match {
              case Working()  =>
                giveup = false
                transferTickets(Child(i), 1 + checkTickets() / numActiveKids)
              case _ => ()
            }
        if(giveup ){ 
          returnNode(GaveUp())
        }
        case _ =>
          transferTickets(Parent(), checkTickets())          
      }
    }


  def timeout(): Unit = {
    println("ornode timeout")
  }

  def abort(): Unit = {

    println("ornode abort")
  }

  def handleMessage(msg: Any): Unit = {
    ()
  }


  def childReturned(child: Int, v: Any): Unit = v match {
    case Proved(rl) =>
      returnNode(Proved(rl))
    case Disproved() =>
    case GaveUp() =>
    case _ => println("got weird return value " + v)
  }

  override def toString(): String = {
    "OrNode( " + P.string_of_Goal(goal) + ")"
  } 


}



@serializable
class AndNode(
              rl: String,
              g: Sequent, 
              strategy: SearchStrategy,
              ps: List[Sequent])

  extends DLNode() {

  val goal = g
  val rule = rl

  var workedHereYet = false


  var numOpenChildren = ps.length
  
  def childReturned(child: Int, v: Any): Unit = v match {
    case Proved(rl) =>
      println("node " + nodeID + ". child returned: " + child + " " + v)
      numOpenChildren -= 1
      println("numOpenChildren =  " + numOpenChildren)
      if(numOpenChildren <= 0){
        returnNode(Proved(rule))
      } 
    case Disproved() =>
      returnNode(Disproved())
    case GaveUp() =>
      returnNode(GaveUp())
    case _ => println("got weird return value " + v)
  }

  def handleMessage(msg: Any): Unit = msg match {
    case _ => ()
  }

  override def toString(): String = {
    "AndNode" // + P.string_of_Goal(goal) + ")"
  } 


  def workHere(timeslice: Long): Unit =  {
   statusLock.synchronized{
    checkStatus() match {
      case Working() =>
         if(! workedHereYet){
          for(sq <- ps) {
           val kid = new OrNode(sq)
           newChild(kid)
          }
          workedHereYet = true
        } 

        if(checkTickets() > 0){
          strategy match {
            case DepthFirst() =>
              for(i <- childrenStatus.indices.reverse){
                childrenStatus(i).get match {
                  case Working() =>
                    transferTickets(Child(i), checkTickets())
                  return ()
                  case _ =>
                }
              }
            // if we get here, there are no active children.
            // shouldn't happen
            //  returnNode(GaveUp())
              println("childrenStatus:" + childrenStatus)
              println("status: " + checkStatus())

              throw new Error("no active children")
            case BreadthFirst() =>
//              status = null
//              receiveTickets(10)
              if(numOpenChildren == 0) 
                throw new Error("no open children. (shouldn't happen)")
              val tpc = checkTickets() / numOpenChildren
              for(i <- childrenStatus.indices.reverse){
                childrenStatus(i).get match {
                  case Working() =>
                    transferTickets(Child(i), tpc + 1)
                  case _ =>
                }
              }
          }
        }
      case _ =>
        transferTickets(Parent(), checkTickets())
    }
   }
  }
   
   
  def timeout(): Unit = {
    ()
  }

  def abort(): Unit = {

    ()
  }

  override def shape() : String = "box"

}  




// this is experimental (doesn't work yet)
@serializable
class ThreadedArithmeticNode( fm: FOFormula)
  extends DLNode() {

  var started = false

  val res = new Ref(None: Option[Boolean])

  val t = new Arithmetic(fm, res)

  var priority: Int = Thread.NORM_PRIORITY

  def workHere(timeSlice: Long): Unit = checkStatus() match {
    case Working() if !started =>
       println("about to attempt quantifier elimination on:\n")
       P.print_FOFormula(fm)
       println()
       CV.start()
       t.start()
       priority = t.getPriority()
    case Working() if !started =>
       CV.start()
       t.setPriority(priority)
    case _ =>
      transferTickets(Parent(), checkTickets())          
  }

  def timeout(): Unit = {
    priority = t.getPriority()
    t.setPriority(Thread.MIN_PRIORITY)
  }

  def abort(): Unit = {
    t.setPriority(Thread.MIN_PRIORITY)
    CV.stop()
  }

  def handleMessage(msg: Any): Unit = {
    ()
  }
    
  def childReturned(c: Int, v: Any) = {
    // no children
    ()
  }

  override def toString(): String = {
    "ArithmeticNode( " + P.string_of_FOFormula(fm)+ ")"
  } 

}

*/


