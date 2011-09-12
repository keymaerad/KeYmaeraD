package DLBanyan
/*
import java.io.BufferedWriter
import java.io.OutputStreamWriter
import java.io.BufferedReader
import java.io.InputStreamReader
*/

import scala.collection.immutable.ListSet
import scala.collection.immutable.HashSet
import scala.collection.mutable.HashMap


import DLBanyan.Util._

final object Prover {


  // for fresh variable names
  val uniqids: HashMap[String, Int] = new HashMap[String,Int];

  def uniqify(s: String): String = {
    val dol = s.indexOf("$")
    val s0 = if(dol == -1) s else s.substring(0,dol);
    uniqids.get(s0) match {
      case None =>
        val s1 = s + "$" + 1;
        uniqids.put(s, 2);
        s1
      case Some(n) =>
        val s1 = s0 + "$" + n;
        uniqids.put(s0, n + 1);
        s1
    }
  }

  def ununiqify(s: String): String = {
    val dol = s.indexOf("$")
    if(dol == -1) s else s.substring(0,dol);
  }

  
  def assoc[A,B](k: A, al: List[(A,B)]): Option[B] = al match {
    case (a,b) :: rest =>
      if( k == a ) Some(b)
      else assoc(k, rest)
    case Nil => None
  }


  def negate(p : Pred): Pred = p match {
    case R("=", args) => R("/=", args)
    case R("/=", args) => R("=", args)
    case R("<", args) => R(">=", args)
    case R("<=", args) => R(">", args)
    case R(">=", args) => R("<", args)
    case R(">", args) => R("<=", args)
    case _ =>
      throw new Error("can't negate: " + p)
  }

  // Indicate whether, e.g.,  we can apply substitution safely. 
  def firstorder(fm: Formula): Boolean = fm match {
    case True | False => true
    case Atom(R(r,ps)) => true
    case Not(f) => firstorder(f)
    case Binop(_,f1,f2) => 
      firstorder(f1) && firstorder(f2)
    case Quantifier(_,_,v,f) =>
      firstorder(f)
    case Modality(_,_,_) => false
    case _ => false
  }


  def canQE_Term(sig:Map[String,(List[Sort],Sort)]) : Term =>  Boolean 
   = tm => tm match {
    case Fn(f, args) if List("+","-", "*", "/", "^").contains(f) =>
      args.forall(canQE_Term(sig))
    case Fn(f, arg::args) => false
    case Fn(f, Nil) =>
      sig.get(f) match {
        case Some((_, Real)) => true
        case None => true // assume that it's real-valued
        case _ => false
      }
    case _ => true
  }

  // Indicate whether, e.g.,  we can apply substitution safely. 
  def canQE(fm: Formula, sig : Map[String,(List[Sort],Sort)]): Boolean 
   = fm match {
    case True | False => true
    case Atom(R(r,ps)) if List("=","<", ">", ">=", "<=").contains(r) => 
      ps.forall(canQE_Term(sig))
    case Not(f) => canQE(f,sig)
    case Binop(_,f1,f2) => 
      canQE(f1,sig) && canQE(f2,sig)
    case Quantifier(_,Real,v,f) =>
      canQE(f,sig)
    case _ => false
  }
  
  def totalDerivTerm(forall_i: Option[String], 
                     d: List[(Fn, Term)], 
                     tm: Term) : Term = tm match {
    case Fn("+", List(t1, t2)) =>
      AM.tsimplify(
        Fn("+", List(totalDerivTerm(forall_i, d, t1),
                     totalDerivTerm(forall_i, d, t2)))
      )
    case Fn("-", List(t1, t2)) =>
      AM.tsimplify(Fn("-", List(totalDerivTerm(forall_i, d, t1), 
                                totalDerivTerm(forall_i, d, t2))))
    case Fn("-", List(t1)) =>
      Fn("-", List( totalDerivTerm(forall_i, d, t1)))
    case Fn("*", List(t1, t2)) =>
      AM.tsimplify(
        Fn("+", List(AM.tsimplify (Fn("*", List(totalDerivTerm(forall_i, d, t1), t2))),
                     AM.tsimplify( Fn("*", List(t1,totalDerivTerm(forall_i, d, t2))))))
      )
    case Fn("/", List(t1, Num(n))) =>
      AM.tsimplify( Fn("/", List( totalDerivTerm(forall_i, d, t1), Num(n))) )
    case Fn("^", List(t1, Num(n))) =>
      if(n == Exact.Integer(2)) {
        Fn("*", 
           List(Num(n),  
                Fn("*", List(t1,
                             totalDerivTerm(forall_i, d, t1 )))))
      } else { 
        Fn("*", 
           List(Num(n),  
                Fn("*", List(Fn("^",List(t1,Num(n-Exact.Integer(1)))),
                             totalDerivTerm(forall_i, d, t1 )))))
      }
    case Var(s) =>  
      Num(Exact.Integer(0))
    case Fn(f, Nil) =>  assoc(tm,d) match {
      case Some(x) => x
      case None => Num(Exact.Integer(0))
    }
    case Fn(f, List(i)) =>
      forall_i match {
        case None => Num(Exact.Integer(0))
        case Some(ii) =>
          assoc(Fn(f, List(Var(ii))), d) match {
            case Some(x) => x
            case None => Num(Exact.Integer(0))
          }
      }
    case Fn(f,_) => throw new Error("don't know how to take derivative of " + f)
    case Num(n) => Num(Exact.Integer(0))

  }


  // Precondition: |fm| is in negation normal form.
  // TODO handle other cases
  def totalDerivAux(forall_i: Option[String],
                    d: List[(Fn,Term)],
                    fm: Formula) : Formula 
    = fm match {
      case True => True
      case False => False
      case Atom(R(r, tms)) =>
        val tms1 = tms.map( (t: Term) =>  totalDerivTerm(forall_i, d, t))
        tms1 match {
          case Num(n1)::Num(n2)::nil if n1.is_zero && n2.is_zero =>
            True
          case _ => 
            Atom(R(r, tms1))
        }
      case Not(Atom(p)) =>
        totalDerivAux(forall_i, d, Atom(negate(p)))
      case Binop(And, f1, f2) =>
        Binop(And, totalDerivAux(forall_i, d, f1), totalDerivAux(forall_i, d, f2))

       
      case Binop(Or,f1,f2) =>
        Binop(And, // N.B. this is not "or"!
              totalDerivAux(forall_i, d, f1), 
              totalDerivAux(forall_i, d, f2))
      
      //case Iff(f1,f2) => Iff(totalDerivAux(d,f1), totalDerivAux(d,f2))
      case Quantifier(Forall, s, v, f) =>
        Quantifier(Forall, s, v, totalDerivAux(forall_i, d, f))
      case _ => 
        throw new Error("can't take total derivative of formula " +
                        fm)
    }
    

  def totalDeriv(forall_i: Option[String], 
                 d: List[(Fn,Term)],
                 fm: Formula) : Formula = {
    totalDerivAux(forall_i, d, Util.nnf(fm))
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
    case Binop(And,fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case Binop(Or,fm1,fm2)  => openSet(fm1) & openSet(fm2)
    case _ => false
  }

  def setClosure(fm: Formula): Formula = fm match {
    case Atom(R("<", ts)) => Atom(R("<=", ts))
    case Atom(R(">", ts)) => Atom(R(">=", ts))
    case Binop(And,fm1,fm2)  => Binop(And,setClosure(fm1), setClosure(fm2))
    case Binop(Or,fm1,fm2)  => Binop(Or,setClosure(fm1),setClosure(fm2))
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
    case Binop(c,f1,f2) => 
      Binop(c,rename_Formula(xold,xnew,f1),rename_Formula(xold,xnew,f2))
    case Quantifier(q,c,v,f) if v == xold =>
      val v1 = uniqify(v)
      val f1 = rename_Formula(v,v1,f)
      Quantifier(q, c, v1, rename_Formula(xold, xnew, f1))
    case Quantifier(q,c,v,f) =>
      Quantifier(q, c, v, rename_Formula(xold,xnew,f))      
    case Modality(m,hp,phi) =>
      Modality(m,rename_HP(xold,xnew,hp), rename_Formula(xold,xnew,phi))

  }

  def rename_HP(xold:String,xnew:String,hp:HP):HP = hp match {
    case Assign(vs) =>
      val vs1 = vs.map( v => {
        val (Fn(f,args), t) = v;
        val args1 = args.map(a => rename_Term(xold,xnew,a));
        val t1 = rename_Term(xold,xnew,t);
        (Fn(f,args1),t1)});
      Assign(vs1)
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
    case Binop(c,f1,f2) => 
      Binop(c,onterms_Formula(g,f1),onterms_Formula(g,f2))
    case Quantifier(q, c, v,f) =>
      Quantifier(q, c, v, onterms_Formula(g,f))      
    case Modality(m,hp,phi) =>
      Modality(m,onterms_HP(g,hp), onterms_Formula(g,phi))
  }

  def onterms_HP(g : Term => Term,hp:HP):HP = {
    val replace: ((Fn, Term)) => (Fn, Term) = vt => {
      val (v,t) = vt
      val Fn(f,args) =  g(v)
      val t1 = g(t)
      (Fn(f,args),t1)
    }    ;
    hp match {
      case Assign(vs) =>
        Assign(vs.map(replace))
      case AssignQuantified(i,c,vs) =>
        AssignQuantified(i,c, vs.map(replace)  )
      case AssignAny(x) =>
        val Fn(f,args) = g(x) // error if g changes x to a nonfunction
        AssignAny(Fn(f,args))
      case AssignAnyQuantified(i,c,x) =>
        val Fn(f,args) = g(x) // error if g changes x to a nonfunction
        AssignAnyQuantified(i,c,Fn(f,args))
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
        Evolve(derivs.map( replace), 
               onterms_Formula(g,fm),
               inv_hints.map(f => onterms_Formula(g,f)),
               sols.map(f => onterms_Formula(g,f)))
      case EvolveQuantified(i,c, vs, h, sols) =>
        EvolveQuantified(i,c,
                         vs.map(replace),
                         onterms_Formula(g,h),
                         sols.map(f => onterms_Formula(g,f)))
      
    }
  }

// do generic fold over terms

  def overterms_Formula[B](g : Term => B => B,
                           fm: Formula, 
                           b : B) : B = fm match {
    case True | False => b
    case Atom(R(r,ps)) => 
      ps.foldRight(b)((x,y) => g(x)(y))
    case Not(f1) => overterms_Formula(g,f1,b)
    case Binop(c,f1,f2) => 
      overterms_Formula(g,f1,
                        overterms_Formula(g,f2,b))
    case Quantifier(q, c, v,f) =>
      overterms_Formula(g,f,b)
    case Modality(m,hp,phi) =>
      overterms_HP(g,hp,
                   overterms_Formula(g,phi,b))
  }

  def overterms_HP[B](g : Term => B => B, hp:HP, b: B):B = {
    val foldit: (List[(Fn, Term)]) => B => B = vs => b0 => {
      val (fs,ts) = vs.unzip
      val fsr = fs.foldRight(b0)((x,y) => g(x)(y))
      val tsr = fs.foldRight(fsr)((x,y) => g(x)(y))
      tsr
    }    ;
    hp match {
      case Assign(vs) =>
        foldit(vs)(b)
      case AssignQuantified(i,c,vs) =>
        foldit(vs)(b)
      case AssignAny(x) =>
        b
      case AssignAnyQuantified(i,c,f) =>
        b // is this right?
      case Check(fm) =>
        overterms_Formula(g,fm,b)
      case Seq(p,q) => 
        overterms_HP(g,p,
                     overterms_HP(g,q,b))
      case Choose(p,q) => 
        overterms_HP(g,p,
                     overterms_HP(g,q,b))
      case Loop(p,fm, inv_hints) =>
          overterms_HP(g,p, 
                       overterms_Formula(g,fm,b))
      case Evolve(derivs, fm, inv_hints, sols) =>
        overterms_Formula(g,fm,foldit(derivs)( b))
      case EvolveQuantified(i,c, vs, h, sols) =>
        overterms_Formula(g,h,foldit(vs)(b))
      
    }
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


// "var"ifying functions
  def varifyFn_Term(fold: String, fnew: String, tm: Term): Term = tm match {
    case Fn(f, ps) =>
      if(f == fold) {
        Var(fnew)
      } else{
        Fn(f, ps.map(p => varifyFn_Term(fold, fnew,p)))
      }
    case _ => tm
  }

  def varifyFn(fold: String, fnew: String, fm : Formula) : Formula = 
    onterms_Formula(t => varifyFn_Term(fold,fnew,t),fm)



  def hasFn_Term(f: String, tm: Term) : Boolean = tm match {
    case Fn(f1, ps) if f1 == f => true
    case Fn(f1, ps) =>
      val psr = ps.map(p => hasFn_Term(f,p))
      psr.contains(true);
    case _ => false
  }

  def hasFn_Formula(f: String, fm: Formula) : Boolean = 
    AM.overatoms((a: Pred) => (r1: Boolean) => 
      {
        val R(r,ps) = a;
        val psr = ps.map(p => hasFn_Term(f,p))
        val res = psr.contains(true)
        r1 || res
      }, fm , false)


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



  def substitute_HP(xold: String,
                    xnew: Term,
                    hp : HP) : HP = {
    val subst : Term => Term = tm => tm match{
      case Var(x) if x == xold => xnew
      case _ => tm
    }
    onterms_HP(subst, hp)
  }




  def substitute_Formula1(xold: String,
                      xnew: Term,
                      xnew_fv: Set[String],
                      fm: Formula): Formula = fm match {
    case True | False => fm
    case Atom(R(r,ps)) => 
      Atom(R(r, ps.map(p => substitute_Term(xold,xnew,p))))
    case Not(f) => Not(substitute_Formula1(xold,xnew,xnew_fv,f))
    case Binop(c,f1,f2) => 
      Binop(c,substitute_Formula1(xold,xnew,xnew_fv,f1),
          substitute_Formula1(xold,xnew,xnew_fv,f2))
    case Quantifier(q,c,v,f) =>
      if( ! xnew_fv.contains(v)){
        Quantifier(q,c,v, substitute_Formula1(xold,xnew, xnew_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Quantifier(q,c,v1,substitute_Formula1(xold,xnew, xnew_fv, f1))
      }
    //XXX  we don't check for captured function symbols!
    // This is okay if we uniqify function symbols in the
    // xnew.
    case Modality(m, hp, f) =>
      Modality(m, substitute_HP(xold,xnew,hp),
                 substitute_Formula1(xold,xnew,xnew_fv,f))
  }

  def substitute_Formula(xold: String, xnew: Term, fm: Formula): Formula = {
    val vs = varsOfTerm(xnew)
    substitute_Formula1(xold,xnew, HashSet.empty ++ vs, fm)
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
    case Binop(c,f1,f2) => 
      Binop(c,simul_substitute_Formula1(subs,new_fv,f1),
          simul_substitute_Formula1(subs,new_fv,f2))
    case Quantifier(q,c,v,f) =>
      if( ! new_fv.contains(v)){
        Quantifier(q,c,v, simul_substitute_Formula1(subs, new_fv, f))
      } else {
        val v1 = uniqify(v)
        val f1 = rename_Formula(v,v1,f)
        Quantifier(q,c,v1,simul_substitute_Formula1(subs, new_fv, f1))
      }
  }

  def simul_substitute_Formula(                      
                      subs: List[(String,Term)],
                      fm: Formula): Formula =  {
    val ts = subs.map(_._2)
    val vs = HashSet.empty ++ (ts.map(varsOfTerm).flatten[String])
    simul_substitute_Formula1(subs, vs, fm)
  }


// so we can write a formula as a substitution

  def extract_Term(tm_ex: Term,  tm : Term) : Term => Term = tm match {
    case _ if tm == tm_ex =>     
       tm1 => tm1
    case Fn(f, args) =>
      val argsfn = (tm1: Term) => args.map(a =>  extract_Term(tm_ex,a)(tm1))
      tm1 => Fn(f,argsfn(tm1)  )
    case _ => 
      tm1 => tm
  }

  def extract_HP(tm_ex: Term, hp : HP) : Term => HP = hp match {
    case _ if false => 
      tm1 => hp
    // TODO
  }


  def extract(tm_ex : Term, fm: Formula ) : (Term => Formula) = fm match {
    case True | False => 
      tm1 => fm
    case Atom(R(r,args)) => 
      val argsfn = (tm1: Term) => args.map(a =>  extract_Term(tm_ex,a)(tm1))
      tm1 => Atom(R(r,argsfn(tm1)))
    case Not(f) =>
      tm1 => Not(extract(tm_ex, f)(tm1))
    case Binop(c, f1, f2) =>
      tm1 => Binop(c, extract(tm_ex,f1)(tm1), extract(tm_ex,f2)(tm1))
    case Quantifier(q, c, v,f) => 
      // should we do some alpha renaming magic here?
      tm1 => Quantifier(q, c, v, extract(tm_ex,f)(tm1))
    case Modality(m, hp, f) =>
      tm1 => Modality(m,hp, extract(tm_ex,f)(tm1))
  }


  /* If we find an update, return a formula with a hole where it was, and
   *  the formula that was in that hole.
   */ 
  def extract_update(fm: Formula) : Option[(Formula => Formula, Formula)] = fm match {
    case True | False | Atom(_) => 
      None
    case Not(f) =>
      extract_update_aux(x => Not(x), f)
    case Binop(c, fm1, fm2) =>
      extract_update(fm1) match {
        case None => extract_update_aux(x => Binop(c,fm1,x), fm2)
        case Some((fn1,fm0)) => Some((x => Binop(c,fn1(x),fm2),fm0))
      }
    case Quantifier(q, c, v,f) => 
      extract_update_aux(x => Quantifier(q,c,v,x), f)
    case Modality(m, AssignQuantified(i,srt,vs), f) =>
      Some((x => x ,fm))
    case Modality(m, hp, f) =>
      extract_update_aux(x => Modality(m,hp,x), f)

  }

  def extract_update_aux(g: Formula => Formula, fm: Formula) 
     : Option[(Formula => Formula, Formula)] = extract_update(fm) match {
        case None => None
        case Some((fn1, f1)) => 
          Some(((fm1 => g(fn1(fm1)) ), f1))
     }


  

  type Subst = Map[String,Term] 

  val nilmap = scala.collection.immutable.HashMap[String,Term]()

  def unify_Terms(subs: Subst, tms1 : List[Term], tms2 : List[Term]) : Option[Subst] 
      = (tms1, tms2) match {
        case (Nil, Nil) => Some(subs)
        case (tm1::rest1, tm2::rest2) =>
          unify_Term(subs, tm1,tm2) match {
            case None =>  None
            case Some(subs1) => unify_Terms(subs1,rest1,rest2) 
          }
        case _ => None

      }


    // tm1 is specific, tm2 has free variables.
    // figure out what to associate to those free variables in to get tm1.
  def unify_Term(subs: Subst, tm1 : Term, tm2 : Term) : Option[Subst] 
  = (tm1,tm2) match {
    case (Fn(f1,args1), Fn(f2,args2)) if f1 == f2 =>
      unify_Terms(subs, args1,args2)
    case (tm1, Var(x)) =>
      subs.get(x) match {
        case None =>
          Some(subs + ((x,tm1)))
        case Some(tm)  if tm1 == tm =>
          Some(subs)
        case _ =>
          None
      }
    case (Num(n), Num(m)) if n.==(m) =>
      Some(subs)
    case _ =>  None
  }

  def unify_Formulas(subs: Subst, 
                     fms1 : List[Formula], 
                     fms2 : List[Formula]) : Option[Subst] 
      = (fms1, fms2) match {
        case (Nil, Nil) => Some(subs)
        case (fm1::rest1, fm2::rest2) =>
          unify_Formula(subs, fm1,fm2) match {
            case None => None
            case Some(subs1) => unify_Formulas(subs1,rest1,rest2) 
          }
        case _ => 
          None
      }

    // fm1 is specific, fm2 has free variables.
    // figure out what to associate to those free variables in to get fm1.
  def unify_Formula(subs: Subst, fm1 : Formula, fm2 : Formula) : Option[Subst] 
  = (fm1,fm2) match {
    case (True,True) | (False, False) => 
      Some(subs)
    case (Atom(R(r1,args1)), Atom(R(r2,args2))) if r1 == r2 => 
      unify_Terms(subs,args1,args2)
    case (Not(f1), Not(f2) )=>
      unify_Formula(subs,f1,f2)
    case (Binop(op1,f1,g1), Binop(op2, f2,g2)) if op1 == op2 => 
      unify_Formulas(subs,List(f1,g1),List(f2,g2))
    case (Quantifier(qt1, srt1, bv1, f1), Quantifier(qt2, srt2, bv2, f2)) 
           if qt1 == qt2 && srt1 == srt2 =>
             val f3 = rename_Formula(bv2, bv1, f2)
             unify_Formula(subs, f1,f3)
    case _ => None
  }


  def unify(fm1 : Formula, fm2 : Formula) : Option[Subst] = {
    unify_Formula(nilmap, fm1,fm2)
  }


  def infersort(sig: Map[String, (List[Sort],Sort)], tm: Term) : Sort = tm match {
    case Fn(f,args) =>
      sig.get(f) match {
        case None if List("+", "-", "*", "/", "^").contains(f) => Real
        case Some((_,srt)) => srt
        case _ => Real // Perhaps should throw error here.
      }
    case Num(_) => 
      Real
    case Var(_) =>
      Real // XXX ??
  }
                

  // not yet fully implemented
  def alphaeq(fm1: Formula, fm2: Formula) : Boolean = (fm1,fm2) match {
    case (Not(p1), Not(p2)) =>
      alphaeq(p1,p2) 
    case (Binop(o1,p1,q1), Binop(o2,p2,q2)) if o1 == o2 =>
      alphaeq(p1,p2) && alphaeq(q1,q2)
    case (Quantifier(q1,c1,i1, f1), Quantifier(q2,c2,i2,f2)) if q1 == q2 && c1 == c2 =>
      alphaeq(f1, rename_Formula(i2,i1,f2))
    case _ => fm1 == fm2
  }





}




