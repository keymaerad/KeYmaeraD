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


  // Indicate whether we can apply quantifier elimination.
  def firstorder(fm: Formula): Boolean = fm match {
    case True | False => true
    case Atom(R(r,ps)) => true
    case Not(f) => firstorder(f)
    case And(f1,f2) => 
      firstorder(f1) && firstorder(f2)
    case Or(f1,f2) => 
      firstorder(f1) && firstorder(f2)
    case Imp(f1,f2) => 
      firstorder(f1) && firstorder(f2)
    case Iff(f1,f2) => 
      firstorder(f1) && firstorder(f2)
    case Exists(v,f) =>
      firstorder(f)
    case Forall(v,f) =>
      firstorder(f)
    case Box(_,_) => false
    case Diamond(_,_) => false
    case _ => false
  }

  def plugin(fm : Formula, fmctxt: FormulaCtxt): Formula = fmctxt match {
    case Hole => 
      fm
    case NotCtxt(f) =>
      Not(plugin(fm, f))
    case AndCtxt1(f1, f2) =>
      And(plugin(fm, f1), f2)
    case AndCtxt2(f1, f2) =>
      And(f1,plugin(fm, f2))
    case OrCtxt1(f1, f2) =>
      Or(plugin(fm, f1), f2)
    case OrCtxt2(f1, f2) =>
      Or(f1,plugin(fm, f2))
    case ImpCtxt1(f1, f2) =>
      Imp(plugin(fm, f1), f2)
    case ImpCtxt2(f1, f2) =>
      Imp(f1,plugin(fm, f2))
    case IffCtxt1(f1, f2) =>
      Iff(plugin(fm, f1), f2)
    case IffCtxt2(f1, f2) =>
      Iff(f1,plugin(fm, f2))
    case ExistsCtxt(v, f) =>
      Exists(v, plugin(fm,f))
    case ForallCtxt(v, f) =>
      Forall(v, plugin(fm,f))
    case ExistsOfSortCtxt(v, c, f) =>
      ExistsOfSort(v, c, plugin(fm,f))
    case ForallOfSortCtxt(v, c, f) =>
      ForallOfSort(v, c, plugin(fm,f))
    case BoxCtxt(hp, rest) =>
      Box(hp, plugin(fm,rest))
    case DiamondCtxt(hp, rest) =>
      Diamond(hp, plugin(fm,rest))

  }


  def totalDerivTerm(d: List[(Fn, Term)], tm: Term) : Term = tm match {
    case Var(s) =>  
      Num(Exact.Integer(0))
      //assoc(s,d) match {
      //case Some(x) => x
      //case None => Num(Exact.Integer(0))
    //}
    case Fn(f,Nil) =>  assoc(tm,d) match {
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
  def totalDeriv(d: List[(Fn,Term)], fm: Formula) : Formula 
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
                      //P.string_of_Formula(fm))

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
  def openSet(fm: Formula): Boolean = fm match {
    case Atom(R("<", _)) => true
    case Atom(R(">", _)) => true
    case And(fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case Or(fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case _ => false
  }

  def setClosure(fm: Formula): Formula = fm match {
    case Atom(R("<", ts)) => Atom(R("<=", ts))
    case Atom(R(">", ts)) => Atom(R(">=", ts))
    case And(fm1,fm2)  => And(setClosure(fm1), setClosure(fm2))
    case Or(fm1,fm2)  => Or(setClosure(fm1),setClosure(fm2))
    case _ => throw new Error("unsupported setClosure")
  }



// alpha-renaming for logical variables.
  def rename_Term(xold: String,
                 xnew: String,
                 tm: Term): Term = tm match {
    case Var(x) if x == xold =>
      Var(xnew)
    case Fn(f, ps) =>
      val fnew = f // if(f == xold) xnew else f
      Fn(fnew, ps.map(p => rename_Term(xold, xnew,p)))
    case _ => tm
  }

  def rename_Formula(xold: String,
                      xnew: String,
                      fm: Formula): Formula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => rename_Term(xold,xnew,p))))
    case Not(f) => Not(rename_Formula(xold,xnew,f))
    case And(f1,f2) => 
      And(rename_Formula(xold,xnew,f1),rename_Formula(xold,xnew,f2))
    case Or(f1,f2) => 
      Or(rename_Formula(xold,xnew,f1),rename_Formula(xold,xnew,f2))
    case Imp(f1,f2) => 
      Imp(rename_Formula(xold,xnew,f1),rename_Formula(xold,xnew,f2))
    case Iff(f1,f2) => 
      Iff(rename_Formula(xold,xnew,f1),rename_Formula(xold,xnew,f2))
    case Exists(v,f) if v == xold =>
      val v1 = uniqify(v)
      val f1 = rename_Formula(v,v1,f)
      Exists(v1, rename_Formula(xold, xnew, f1))
    case Exists(v,f) =>
      Exists(v, rename_Formula(xold,xnew,f))      
    case Forall(v,f) if v == xold =>
      val v1 = uniqify(v)
      val f1 = rename_Formula(v,v1,f)
      Forall(v1, rename_Formula(xold, xnew, f1))
    case Forall(v,f) => 
      Forall(v, rename_Formula(xold,xnew,f))
/*    case ExistsOfSort(v,c,f) if v == xold =>
      val v1 = uniqify(v)
      val f1 = rename_Formula(v,v1,f)
      ExistsOfSort(v1, c, rename_Formula(xold, xnew, f1))
    case ExistsOfSort(v,c,f)  =>
      val v1 = uniqify(v)
      val f1 = rename_Formula(v,v1,f)
      ExistsOfSort(v1, c, rename_Formula(xold, xnew, f1)) */
    case Box(hp,phi) =>
      Box(rename_HP(xold,xnew,hp), rename_Formula(xold,xnew,phi))
    case Diamond(hp,phi) =>
      Diamond(rename_HP(xold,xnew,hp), rename_Formula(xold,xnew,phi))

  }

  def rename_HP(xold:String,xnew:String,hp:HP):HP = hp match {
    case Assign(Fn(f,args), t) =>
      val args1 = args.map(a => rename_Term(xold,xnew,a))
      val t1 = rename_Term(xold,xnew,t)
      Assign(Fn(f,args1),t1)
    case AssignAny(Fn(f,args)) =>
      val args1 = args.map(a => rename_Term(xold,xnew,a))
      AssignAny(Fn(f,args1))
    case Check(fm) =>
      Check(rename_Formula(xold,xnew,fm))
    case Seq(p,q) => 
      Seq(rename_HP(xold,xnew,p), rename_HP(xold,xnew,q))
    case Choose(p1,p2) => 
      Choose(rename_HP(xold,xnew,p1), rename_HP(xold,xnew,p2))
    case Loop(p,fm, inv_hints) =>
      Loop(rename_HP(xold,xnew,p), 
           rename_Formula(xold,xnew,fm), 
           inv_hints.map(f => rename_Formula(xold,xnew,f)))
    case Evolve(derivs, fm, inv_hints, sols) =>
      val replace_deriv: ((Fn, Term)) => (Fn, Term) = vt => {
        val (Fn(f,args),t) = vt
        val args1 =  args.map(a => rename_Term(xold,xnew,a))
        val t1 = rename_Term(xold,xnew,t)
        (Fn(f,args1),t1)
      }
      Evolve(derivs.map( replace_deriv), 
             rename_Formula(xold,xnew,fm),
             inv_hints.map(f => rename_Formula(xold,xnew,f)),
             sols.map(f => rename_Formula(xold,xnew,f)))
      
  }



// do generic thing to terms

  def onterms_Formula(g : Term => Term,
                      fm: Formula): Formula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => g(p))))
    case Not(f1) => Not(onterms_Formula(g,f1))
    case And(f1,f2) => 
      And(onterms_Formula(g,f1),onterms_Formula(g,f2))
    case Or(f1,f2) => 
      Or(onterms_Formula(g,f1),onterms_Formula(g,f2))
    case Imp(f1,f2) => 
      Imp(onterms_Formula(g,f1),onterms_Formula(g,f2))
    case Iff(f1,f2) => 
      Iff(onterms_Formula(g,f1),onterms_Formula(g,f2))
    case Exists(v,f) =>
      Exists(v, onterms_Formula(g,f))      
    case Forall(v,f) =>
      Forall(v, onterms_Formula(g,f))      
    case ExistsOfSort(v,c,f) =>
      ExistsOfSort(v, c, onterms_Formula(g,f))      
    case ForallOfSort(v,c,f) =>
      ForallOfSort(v, c, onterms_Formula(g,f))      
    case Box(hp,phi) =>
      Box(onterms_HP(g,hp), onterms_Formula(g,phi))
    case Diamond(hp,phi) =>
      Diamond(onterms_HP(g,hp), onterms_Formula(g,phi))

  }

  def onterms_HP(g : Term => Term,hp:HP):HP = hp match {
    case Assign(x, t) =>
      val Fn(f,args) = g(x) // error if g changes x to a nonfunction
      val t1 = g(t)
      Assign(Fn(f,args),t1)
    case AssignAny(x) =>
      val Fn(f,args) = g(x) // error if g changes x to a nonfunction
      AssignAny(Fn(f,args))
    case Check(fm) =>
      Check(onterms_Formula(g,fm))
    case Seq(p,q) => 
      Seq(onterms_HP(g,p), onterms_HP(g,q))
    case Choose(p,q) => 
      Choose(onterms_HP(g,p), onterms_HP(g,q))
    case Loop(p,fm, inv_hints) =>
      Loop(onterms_HP(g,p), 
           onterms_Formula(g,fm), 
           inv_hints.map(f => onterms_Formula(g,f)))
    case Evolve(derivs, fm, inv_hints, sols) =>
      val replace_deriv: ((Fn, Term)) => (Fn, Term) = vt => {
        val (v,t) = vt
        val Fn(f,args) =  g(v)
        val t1 = g(t)
        (Fn(f,args),t1)
      }
      Evolve(derivs.map( replace_deriv), 
             onterms_Formula(g,fm),
             inv_hints.map(f => onterms_Formula(g,f)),
             sols.map(f => onterms_Formula(g,f)))
      
  }

// renaming functions
  def renameFn_Term(fold: String, fnew: String, tm: Term): Term = tm match {
    case Fn(f, ps) =>
      val f1 =  if(f == fold) fnew else f
      Fn(f1, ps.map(p => renameFn_Term(fold, fnew,p)))
    case _ => tm
  }

  def renameFn(fold: String, fnew: String, fm : Formula) : Formula = 
    onterms_Formula(t => renameFn_Term(fold,fnew,t),fm)



//

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


  

  def substitute_Formula(xold: String,
                      xnew: Term,
                      xnew_fv: Set[String],
                      fm: Formula): Formula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => substitute_Term(xold,xnew,p))))
    case Not(f) => Not(substitute_Formula(xold,xnew,xnew_fv,f))
    case And(f1,f2) => 
      And(substitute_Formula(xold,xnew,xnew_fv,f1),
          substitute_Formula(xold,xnew,xnew_fv,f2))
    case Or(f1,f2) => 
      Or(substitute_Formula(xold,xnew,xnew_fv,f1),
          substitute_Formula(xold,xnew,xnew_fv,f2))
    case Imp(f1,f2) => 
      Imp(substitute_Formula(xold,xnew,xnew_fv,f1),
          substitute_Formula(xold,xnew,xnew_fv,f2))
    case Iff(f1,f2) => 
      Iff(substitute_Formula(xold,xnew,xnew_fv,f1),
          substitute_Formula(xold,xnew,xnew_fv,f2))
    case Exists(v,f) =>
      if( ! xnew_fv.contains(v)){
        Exists(v, substitute_Formula(xold,xnew, xnew_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Exists(v1,substitute_Formula(xold,xnew, xnew_fv, f1))
      }
    case Forall(v,f) =>
      if( ! xnew_fv.contains(v)){
        Forall(v, substitute_Formula(xold,xnew, xnew_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Forall(v1,substitute_Formula(xold,xnew, xnew_fv, f1))
      }
  }


  def simul_substitute_Formula1(
                      subs: List[(String,Term)],
                      new_fv: Set[String],
                      fm: Formula): Formula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => simul_substitute_Term(subs,p))))
    case Not(f) => 
      Not(simul_substitute_Formula1(subs,new_fv,f))
    case And(f1,f2) => 
      And(simul_substitute_Formula1(subs,new_fv,f1),
          simul_substitute_Formula1(subs,new_fv,f2))
    case Or(f1,f2) => 
      Or(simul_substitute_Formula1(subs,new_fv,f1),
          simul_substitute_Formula1(subs,new_fv,f2))
    case Imp(f1,f2) => 
      Imp(simul_substitute_Formula1(subs,new_fv,f1),
          simul_substitute_Formula1(subs,new_fv,f2))
    case Iff(f1,f2) => 
      Iff(simul_substitute_Formula1(subs,new_fv,f1),
          simul_substitute_Formula1(subs,new_fv,f2))
    case Exists(v,f) =>
      if( ! new_fv.contains(v)){
        Exists(v, simul_substitute_Formula1(subs, new_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Exists(v1,simul_substitute_Formula1(subs, new_fv, f1))
      }
    case Forall(v,f) =>
      if( ! new_fv.contains(v)){
        Exists(v, simul_substitute_Formula1(subs, new_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Forall(v1,simul_substitute_Formula1(subs, new_fv, f1))
      }
  }

  def simul_substitute_Formula(                      
                      subs: List[(String,Term)],
                      fm: Formula): Formula =  {
    val ts = subs.map(_._2)
    val vs = HashSet.empty ++ (ts.map(varsOfTerm).flatten[String])
    simul_substitute_Formula1(subs, vs, fm)
  }

}




