package DLBanyan
//package prover
//package cohenhormander;

import scala.actors.Actor
import scala.actors.Actor._
//import scala.actors.TIMEOUT

//import banyan._


abstract class Sign
case class Zero() extends Sign
case class Nonzero() extends Sign
case class Positive() extends Sign
case class Negative() extends Sign

object CV {  
  var lock = new Object();
  var keepGoing = true;
  def start() : Unit = {
    lock.synchronized{ //does scala do this better?
       keepGoing = true;
    }
  }
  def stop() : Unit = {
    lock.synchronized{
       keepGoing = false;
    }
  }
}



class CHAbort() extends Exception
class AssocException() extends Exception
class Failure() extends Exception

final object AM {

/* List Utilities
  */

  def nil:List[Term] = Nil;

 
  def assoc[A,B](k: A, al: List[(A,B)]): B = al match {
    case (a,b) :: rest =>
      if( k == a ) b
      else assoc(k, rest)
    case Nil => throw new AssocException()
  }

  def mem[A](x: A, lst: List[A]): Boolean = lst match {
    case e::es => 
      if( e == x ) true
      else mem(x, es)
    case Nil => false
  }
  
  final def index1[A](x: A, lst: List[A], n: Int): Int = lst match {
    case e::es => if(x == e) n
		  else index1(x, es, n + 1)
    case Nil => throw new Failure()
  }


  def index[A](x: A, lst: List[A]): Int = {
    index1(x,lst,0)
  }

  def el[A](i: Int, lst: List[A]): A = lst match {
    case e::es => if(i==0) e
		  else el(i-1, es)
    case Nil => throw new Failure()
  }

  def earlier[A](lst: List[A], x: A, y: A): Boolean = 
    lst match {
      case h::t => 
        y != h && (h == x || earlier(t,x,y))
      case Nil => false
    }
  
/*
  def insertat1[A](n: Int, x: A, lst: List[A], accum: List[A]): List[A] = {
    if (n < 1) (accum.reverse ++ (x :: lst))
    else lst match {
      case e::es => insertat1(n-1,x,es,e::accum)
      case Nil => (x:: accum).reverse
    }
  }
*/

  final def insertat[A](n: Int, x: A, lst: List[A]): List[A] = {
    if(n==0) x::lst else
    lst match {
      case Nil => throw new Error("insertat: list too short.")
      case h::t => h::(insertat(n-1,x,t))
    }
  }



/* we could do this more efficiently. */

/*
  def unions[A](lst: List[List[A]]): List[A] = {
    val lst1 = lst.flatten(identity[List[A]] _) ;
    lst1.removeDuplicates
  }


  def union[A](lst1: List[A], lst2: List[A]): List[A] = {
    (lst1 ++ lst2).removeDuplicates
  }

  def insert[A](x: A, lst: List[A]): List[A] = {
    if(lst.contains(x)) lst
    else x::lst
  }

* */

  def allpairs[A,B](f: (A,A) => B, lst1: List[A], lst2: List[A]): List[B] 
  = lst1 match {
    case e::es => lst2.map((a:A)=>f(e,a)) ++ allpairs(f,es,lst2)
    case Nil => Nil
  }

 //  def setify[A](lst: List[A]): List[A] = lst.removeDuplicates;



  implicit def term2Ordered(t: Term): Ordered[Term] = new Ordered[Term] {
    def compare(that: Term): Int = (t,that) match {
      case (Var(_), Fn(_,_)) => -1
      case (Var(_), Num(_)) => -1
      case (Fn(_,_), Num(_)) => -1
      case (Fn(_,_), Var(_)) => 1
      case (Num(_), Var(_)) => 1
      case (Num(_), Fn(_,_)) => 1
      case (Var(x), Var(y)) => x compare y
      case (Fn(f,fargs), Fn(g,gargs)) => 
        if(f != g) f compare g
        else fargs compare gargs
      case (Num(n), Num(m)) => n compare m
    }
  }

  implicit def fol2Ordered(f: Pred): Ordered[Pred] = new Ordered[Pred] {
    def compare(that: Pred): Int = (f,that) match {
      case (R(s,ps), R(s2,ps2)) => 
        if(s != s2) s compare s2
        else ps compare ps2
    }
  }

  implicit def connective2Orderd(c: Connective): Ordered[Connective] = 
    new Ordered[Connective] {
      def connectiveEnum(c1 : Connective): Int = c1 match {
        case And => 0
        case Or => 1
        case Imp => 2
        case Iff => 3
      }

      def compare(that: Connective): Int = {
        connectiveEnum(c).compare(connectiveEnum(that))
      }
    }


  // yuck. Is there a better way to write this?
  implicit def formula2Ordered(f: Formula): Ordered[Formula] = 
    new Ordered[Formula] {
      def compare(that: Formula): Int = f match {
        case False => if(that == False) 0 else -1
        case True => that match {
          case False => 1
          case True => 0
          case _ => -1
        }
        case Atom(a1) => that match {
          case False | True => 1
          case Atom(a2) => a1 compare a2
          case _ => -1
        }
        case Not(f1) => that match {
          case False | True | Atom(_) => 1
          case Not(f2) => f1 compare f2
          case _ => -1
        }
        case Binop(c,f1,f2) => that match {
          case False | True | Atom(_) | Not(_) => 1
          case Binop(d, g1,g2) =>
            val c1 = c compare d;
            if(c1 != 0)  c1
            else {
              val c2 = f1 compare g1;
              if(c2 != 0) c2
              else f2 compare g2
            }
          case _ => -1
        }
        case Forall(x,f) => that match {
          case False | True | Atom(_) | Not(_) 
             | Binop(_,_,_) => 1
          case Forall(y,g) =>
            val c = x compare y;
            if(c == 0) f compare g
            else c
          case _ => -1
        }
        case Exists(x,f) => that match {
          case Exists(y,g) =>
            val c = x compare y;
            if(c == 0) f compare g
            else c
          case _ => 1
        }
        case _ => 
          throw new Error("nonfirstorder arithmetic")
      }
    }

  
  implicit def formulaList2Ordered(flst: List[Formula])
    : Ordered[List[Formula]] =  new Ordered[List[Formula]] {
      def compare(that: List[Formula]): Int = (flst,that) match {
        case (Nil, Nil) => 0
        case (Nil, _) => -1
        case (_, Nil) => 1
        case (h1::t1, h2::t2) =>
          if (h1==h2) t1 compare t2
          else h1 compare h2

      }
    }

  implicit def list2Ordered[A <% Ordered[A]](flst: List[A])
    : Ordered[List[A]] =  new Ordered[List[A]] {
      def compare(that: List[A]): Int = (flst,that) match {
        case (Nil, Nil) => 0
        case (Nil, _) => -1
        case (_, Nil) => 1
        case (h1::t1, h2::t2) =>
          if (h1==h2) t1 compare t2
          else h1 compare h2
      }
    }
    

  def setifiedp[A <% Ordered[A]](lst: List[A]): Boolean = lst match {
    case x::(rest@(y::_)) => x < y && setifiedp(rest)
    case _ => true
  }

  def setify[A <% Ordered[A]](lst: List[A]) : List[A] = {
    if(setifiedp(lst)) lst else lst.sortWith((x,y) => x < y).distinct
  }

  

  def subtract[A <% Ordered[A]](l1: List[A], l2: List[A]): List[A] = 
    (l1,l2) match {
      case (Nil, _) => Nil
      case (_, Nil) => l1
      case (h1::t1, h2::t2) => 
        if(h1 == h2) subtract(t1,t2)
        else if (h1 < h2) h1::subtract(t1,l2)
        else subtract(l1,t2)
    }

  def psubset[A <% Ordered[A]](lst1: List[A], lst2: List[A]): Boolean = {
    def subset(l1: List[A], l2: List[A]): Boolean = 
      (l1,l2) match {
        case (Nil, _) => true
        case (_, Nil) => false
        case (h1::t1, h2::t2) => 
          if(h1 == h2) subset(t1,t2)
          else if (h1 < h2) false
          else subset(l1,t2)
      }
    def psubset(l1: List[A], l2: List[A]): Boolean = 
      (l1,l2) match {
        case (_, Nil) => false
        case (Nil, _) => true
        case (h1::t1, h2::t2) => 
          if(h1 == h2) psubset(t1,t2)
          else if (h1 < h2) false
          else subset(l1,t2)
      }
    psubset(setify(lst1), setify(lst2))
    }




  // Assumes inputs are setified.
  def intersect[A <% Ordered[A]](l1: List[A], l2: List[A]): List[A] = 
    (l1,l2) match {
      case (Nil, _) => Nil
      case (_, Nil) => Nil
      case (h1::t1, h2::t2) => 
        if(h1 == h2) h1::intersect(t1,t2)
        else if (h1 < h2) intersect(t1,l2)
        else intersect(l1,t2)
    }



  // Assumes inputs are setified.
/*
  def union[A <% Ordered[A]](l1: List[A], l2: List[A]): List[A] = 
    (l1,l2) match {
      case (Nil, _) => l2
      case (_, Nil) => l1
      case (h1::t1, h2::t2) => 
        if(h1 == h2) h1::union(t1,t2)
        else if (h1 < h2) h1::union(t1,l2)
        else h2::union(l1,t2)
    }

*/
 
  def  union[A <% Ordered[A]](lst1: List[A], lst2: List[A]): List[A] =  {
    def union(l1: List[A], l2: List[A]) : List[A] = 
      (l1,l2) match {
        case (Nil, _) => l2
        case (_, Nil) => l1
        case (h1::t1, h2::t2) => 
          if(h1 == h2) h1::union(t1,t2)
          else if (h1 < h2) h1::union(t1,l2)
          else h2::union(l1,t2)
      }
    union(setify(lst1), setify(lst2))
  }



  
  def unions[A <% Ordered[A]](lst: List[List[A]]): List[A] = {
    val lst1 = lst.flatten(identity[List[A]] _) ;
    setify(lst1)
  }


  def insert[A <% Ordered[A]](x:A, s:List[A]): List[A] = {
    union(List(x), s)
  }

/* End list utilities.
 */


/* Simplification.
 */

  def tsimplify1( t: Term): Term = t match {
    case Fn("+",List(Num(m), Num(n))) => Num(m + n)
    case Fn("*",List(Num(m), Num(n))) => Num(m * n)
    case Fn("+",List(Num(n), x)) if n.is_zero => x
    case Fn("+",List(x,Num(n))) if n.is_zero => x
    case Fn("*",List(Num(n), x)) if n.is_zero => zero
    case Fn("*",List(x,Num(n))) if n.is_zero => zero
    case Fn("*",List(Num(n), x)) if n.is_one => x
    case Fn("*",List(x,Num(n))) if n.is_one => x
    case _ => t
  }

  def tsimplify(t: Term): Term = t match {
    case Fn("+",List(e1, e2)) => tsimplify1(
      Fn("+",List(tsimplify(e1), tsimplify(e2))))
    case Fn("*",List(e1, e2)) => tsimplify1(
      Fn("*",List(tsimplify(e1), tsimplify(e2))))
    case _ => tsimplify1(t)
  }



  def psimplify1(fm: Formula): Formula = fm match {
    case Not(False) => True
    case Not(True) => False
    case Not(Not(p)) => p
    case Binop(And, p,False) => False
    case Binop(And, False,p) => False
    case Binop(And,p,True) => p
    case Binop(And,True,p) => p
    case Binop(Or,p,False) => p
    case Binop(Or,False,p) => p
    case Binop(Or,p,True) => True
    case Binop(Or,True,p) => True
    case Binop(Imp,False,p) => True
    case Binop(Imp,p,True) => True
    case Binop(Imp,True,p) => p
    case Binop(Imp,p, False) => Not(p)
    case Binop(Iff,p, True) => p
    case Binop(Iff,True,p) => p
    case Binop(Iff,False, False) => True
    case Binop(Iff,p, False) => Not(p)
    case Binop(Iff,False,p) => Not(p)
    case _ => fm
  }

  /* Simplify a propositional formula. */

  def psimplify(fm: Formula): Formula = fm match {
    case Not(p) => psimplify1(Not(psimplify(p)))
    case Binop(And,p,q) => psimplify1(Binop(And,psimplify(p),psimplify(q)))
    case Binop(Or,p,q) => psimplify1(Binop(Or,psimplify(p),psimplify(q)))
    case Binop(Imp,p,q) => psimplify1(Binop(Imp,psimplify(p),psimplify(q)))
    case Binop(Iff,p,q) => psimplify1(Binop(Iff,psimplify(p),psimplify(q)))
    case _ => fm
  }



  def fvt(tm: Term): List[String] = tm match {
    case Var(x) => List(x)
    case Fn(f,args) => unions(args.map(fvt))
    case Num(_) => Nil
  }


  def vari(fm: Formula): List[String] = fm match {
    case False | True => Nil
    case Atom(R(p,args)) => unions(args.map(fvt))
    case Not(p) => vari(p)
    case Binop(_,p,q) => union(vari(p), vari(q))
    case Forall(x,p) => insert(x, vari(p))
    case Exists(x,p) => insert(x, vari(p))
    case _ => 
      throw new Error("nonfirstorder arithmetic")
  }

  def fv(fm: Formula): List[String] = fm match {
    case False | True => Nil
    case Atom(R(p,args)) => unions(args.map(fvt))
    case Not(p) => fv(p)
    case Binop(_,p,q) => union(fv(p), fv(q))
    case Forall(x,p) => subtract(fv(p) ,List(x))
    case Exists(x,p) => subtract(fv(p),List(x) )
    case _ => 
      throw new Error("nonfirstorder arithmetic")
  }

//  def quantify_fvs(fm: Formula): Formula = 


 
  def simplify1(fm: Formula): Formula = fm match {
    case Forall(x,p) => if( fv(p).contains(x) ) fm
                        else p
    case Exists(x,p) => if( fv(p).contains(x) ) fm
                        else p
    case _ => psimplify1(fm)
  }


  /* Simplify a first order formula. */

  def simplify(fm: Formula): Formula = fm match {
    case Not(p) => simplify1(Not(simplify(p)))
    case Binop(c,p,q) => simplify1(Binop(c,simplify(p),simplify(q)))
    case Forall(x,p) => simplify1(Forall(x,simplify(p)))
    case Exists(x,p) => simplify1(Exists(x,simplify(p)))
    case _ => fm
  }

  

  def distrib[A <% Ordered[A]](s1: List[List[A]], s2: List[List[A]])
   : List[List[A]] = {
    setify(allpairs(union[A],s1,s2))
  }

  def purednf(fm: Formula): List[List[Formula]] = fm match {
    case Binop(And,p,q) => distrib(purednf(p),purednf(q))
    case Binop(Or,p,q) => union(purednf(p),purednf(q))
    case _ => List(List(fm))
  }

  // does this list of formulas have a pair f and Not(f)?
  def trivial(lits: List[Formula]): Boolean = {
    val (pos,neg) = lits.partition(positive(_));
    ! intersect(pos, setify(neg.map(negate))).isEmpty
  }

  def simpdnf(fm: Formula): List[List[Formula]] = {
    if(fm == False) Nil else if(fm == True) List(Nil) else {
    val djs = purednf(nnf(fm)).filter((x:List[Formula]) => ! trivial(x));
    djs.filter(d => !(djs.exists(d_1 => psubset(d_1,d))))
    }
  }

  def dnf(fm: Formula): Formula = {
    list_disj(simpdnf(fm).map(list_conj))
  }

  def nnf(fm: Formula): Formula = fm match {
    case Binop(And,p,q) => Binop(And,nnf(p), nnf(q))
    case Binop(Or,p,q) => Binop(Or,nnf(p), nnf(q))
    case Binop(Imp,p,q) => Binop(Or,nnf(Not(p)), nnf(q))
    case Binop(Iff,p,q) => Binop(Or, Binop(And, nnf(p), nnf(q)), 
                                     Binop(And,nnf(Not(p)), nnf(Not(q))))
    case Not(Not(p)) => p
    case Not(Binop(And,p,q)) => Binop(Or,nnf(Not(p)),nnf(Not(q)))
    case Not(Binop(Or,p,q)) => Binop(And,nnf(Not(p)), nnf(Not(q)))
    case Not(Binop(Imp,p,q)) => Binop(And,nnf(p), nnf(Not(q)))
    case Not(Binop(Iff,p,q)) => Binop(Or,Binop(And,nnf(p),nnf(Not(q))),
                                      Binop(And,nnf(Not(p)),nnf(q)))
    case Forall(x,p) => Forall(x,nnf(p))
    case Exists(x,p) => Exists(x,nnf(p))
    case Not(Forall(x,p)) => Exists(x,nnf(Not(p)))
    case Not(Exists(x,p)) => Forall(x,nnf(Not(p)))
    case _ => fm
  }

  def separate(x: String, cjs: List[Formula]): Formula = {
    val (yes,no) = cjs.partition(c => fv(c).contains(x));
    if(yes == Nil) list_conj(no) 
    else if(no == Nil) Exists(x,list_conj(yes))
    else Binop(And,Exists(x,list_conj(yes)), list_conj(no))
  }
  
  def pushquant(x: String, p: Formula): Formula = {
//    P.print_fol_formula(p);
//    println();
    if(! fv(p).contains(x)) p else {
      val djs = purednf(nnf(p));
      list_disj (djs.map(d => separate(x,d)))
    }
  }

  def miniscope(fm: Formula): Formula = {
    fm match {
    case Not(p) => Not(miniscope(p))
    case Binop(And,p,q) => Binop(And,miniscope(p),miniscope(q))
    case Binop(Or,p,q) => Binop(Or,miniscope(p),miniscope(q))
    case Forall(x,p) => Not(pushquant(x,Not(miniscope(p))))
    case Exists(x,p) => pushquant(x,miniscope(p))
    case _ => fm
  }
  }



  def eval(fm: Formula, v: Pred => Boolean): Boolean = fm match {
    case False => false
    case True => true
    case Atom(x) => v(x)
    case Not(p) => eval(p,v) unary_!
    case Binop(And,p,q) => eval(p,v) && eval(q,v)
    case Binop(Or,p,q) => eval(p,v) || eval(q,v)
    case Binop(Imp,p,q) => (eval(p,v) unary_! ) || eval(q,v)
    case Binop(Iff,p,q) => eval(p,v) == eval(q,v)
    case _ => 
      throw new Error("nonfirstorder arithmetic")
  }

  val operations: List[(String, (Exact.Num,Exact.Num) => Boolean)] = 
    List(("=", (r,s) => r == s),
         ("<", (r,s) => r < s),
         (">", (r,s) => r > s),
         ("<=", (r,s) => r <= s),
         (">=", (r,s) => r >= s))


  def evalc(fm: Formula) : Formula =  {
    onatoms(
      at => at match {
        case R(p,List(Num(n),Num(m))) => 
          try {if(assoc(p,operations)(n,m)) True else False}
          catch { case e => Atom(at)}
        case _ => Atom(at)
      }, fm)
  }


  def mk_and(p: Formula, q: Formula): Formula = Binop(And,p,q);
  def mk_or(p: Formula, q: Formula): Formula = Binop(Or,p,q);

  def conjuncts(fm: Formula): List[Formula] = fm match {
    case Binop(And,p,q) => conjuncts(p) ++ conjuncts(q) 
    case _ => List(fm)
  }

  def disjuncts(fm: Formula): List[Formula] = fm match {
    case Binop(Or,p,q) => disjuncts(p) ++ disjuncts(q) 
    case _ => List(fm)
  }

  // XXX
  def onatoms_HP(f : Pred => Formula, hp : HP) : HP = hp match {
    case _ => hp
  }


  def onatoms(f: Pred => Formula, fm: Formula): Formula  = fm match {
    case Atom(a) => f(a)
    case Not(p) => Not(onatoms(f,p))
    case Binop(c,p,q) => Binop(c,onatoms(f, p), onatoms(f,q))
    case Forall(x,p ) => Forall(x,onatoms(f,p))
    case Exists(x,p ) => Exists(x,onatoms(f,p))
    case ForallOfSort(x,c,p ) => ForallOfSort(x,c,onatoms(f,p))
    case ExistsOfSort(x,c,p ) => ExistsOfSort(x,c,onatoms(f,p))
    case Box(hp, phi) => Box(onatoms_HP(f,hp), onatoms(f,phi))
    case Diamond(hp, phi) => Diamond(onatoms_HP(f,hp), onatoms(f,phi))
    case _ => fm
  }

  def simplify_terms(fm: Formula): Formula = {
    onatoms( fol => fol match {
      case R(r,  List(t1,t2)) => Atom(R(r,List(tsimplify(t1),tsimplify(t2))))
      case _ => throw new Error("simplify terms.")
    }, fm)
  }

  def overatoms[B](f: Pred => B => B, fm: Formula, b: B): B = fm match {
    case Atom(a) => f(a)(b)
    case Not(p) => overatoms(f,p,b)
    case Binop(_,p,q) => overatoms(f, p, overatoms(f,q,b))
    case Forall(x,p ) => overatoms(f, p, b)
    case Exists(x,p ) => overatoms(f, p, b)
    case _ => b
  }

  def atom_union[A <% Ordered[A]](f: Pred => List[A], fm: Formula): List[A] = {
    setify(overatoms( (h:Pred) => (t:List[A]) => f(h) ++ t, fm, Nil))
  }

   
  def list_conj(l: List[Formula]) : Formula = l match {
    case Nil => True
    case f::Nil => f
    case f::fs => Binop(And,f, list_conj(fs))
  }

  def list_disj(l: List[Formula]) : Formula = l match {
    case Nil => False
    case f::Nil => f
    case f::fs => Binop(Or,f, list_disj(fs))
  }


  def qelim(bfn: Formula => Formula, x: String, p: Formula): Formula = {
    val cjs = conjuncts(p);
    val (ycjs, ncjs) = cjs.partition(c => fv(c).contains(x));
    if(ycjs == Nil) p else {
      val q = bfn(Exists(x, list_conj(ycjs)));
      val r = ncjs.foldLeft(q)(mk_and)
      print("|");
      r
    }
  }


  def lift_qelim(afn: (List[String], Formula) => Formula,
                 nfn: Formula => Formula,
                 qfn: List[String] => Formula => Formula) : 
  Formula => Formula = {
    def qelift(vars: List[String], fm: Formula): Formula = fm match {
      case Atom(R(_,_)) => afn(vars,fm)
      case Not(p) => Not(qelift(vars,p))
      case Binop(c,p,q) => 
        Binop(c,qelift(vars,p), qelift(vars,q))
      case Forall(x,p) => Not(qelift(vars,Exists(x,Not(p))))
      case Exists(x,p) => 
        val djs = disjuncts(nfn(qelift(x::vars,p)));
        println("In qelift.  Number of disjuncts = " + djs.length);
        print("["); 
        for(i <- 0 until djs.length){ print(".");}
        print("]\u0008");
        for(i <- 0 until djs.length){ print("\u0008");}
        val djs2 = djs.map(p1 => qelim(qfn(vars), x, p1));
        val r = list_disj(djs2)
        println("]");
        r
//        list_disj(Parallel.pmap(djs, ((p1:Formula) => qelim(qfn(vars), x, p1))))
      case _ => fm
    }
    fm => {
      val m = miniscope(fm);
      val f = fv(fm);
      val q = qelift( f, m);
      val r = simplify(q)
      r
    }
   }


  def negative(fm: Formula) : Boolean = fm match {
    case Not(p) => true
    case _ => false
  }

  def positive(fm: Formula) : Boolean = fm match {
    case Not(p) => false
    case _ => true
  }

  def negate(fm: Formula) : Formula = fm match {
    case Not(p) => p
    case p => Not(p)
  }

  def cnnf(lfn:  Formula => Formula ) : Formula => Formula  =  {
    def cnnf_aux(fm: Formula): Formula = fm match {
      case Binop(And,p,q) => Binop(And,cnnf_aux(p), cnnf_aux(q))
      case Binop(Or,p,q) => Binop(Or,cnnf_aux(p), cnnf_aux(q))
      case Binop(Imp,p,q) => Binop(Or,cnnf_aux(Not(p)), cnnf_aux(q))
      case Binop(Iff,p,q) => Binop(Or,Binop(And,cnnf_aux(p), cnnf_aux(q)),
                          Binop(And,cnnf_aux(Not(p)), cnnf_aux(Not(q))))
      case Not(Not(p)) => cnnf_aux(p)
      case Not(Binop(And,p,q)) => Binop(Or,cnnf_aux(Not(p)), cnnf_aux(Not(q)))
      case Not(Binop(Or,Binop(And,p,q),Binop(And,p_1,r))) if p_1 == negate(p) =>
        Binop(Or,cnnf_aux(Binop(And,p,Not(q))), cnnf_aux(Binop(And,p_1,Not(r))))
      case Not(Binop(Or,p,q)) => Binop(And,cnnf_aux(Not(p)),cnnf_aux(Not(q)))
      case Not(Binop(Imp,p,q)) => Binop(And,cnnf_aux(p), cnnf_aux(Not(q)))
      case Not(Binop(Iff,p,q)) => Binop(Or,Binop(And,cnnf_aux(p),cnnf_aux(Not(q))),
                               Binop(And,cnnf_aux(Not(p)),cnnf_aux(q)))
      case _ => lfn(fm)
    }
    fm => simplify(cnnf_aux(simplify(fm)))
  }
        

      



  val rZero = new Exact.Rational(0);
  val rOne = new Exact.Rational(1);

  val zero = Num(rZero)
  val one = Num(rOne)




/* Polynomial utilities.
 */

  def poly_add(vars: List[String], pol1: Term, pol2: Term): Term = 
    (pol1,pol2) match {
     case (Fn("+", List(c, Fn("*",List(Var(x),p)))),
           Fn("+", List(d, Fn("*",List(Var(y),q))))) =>
             if(earlier(vars,x,y)) poly_ladd(vars, pol2, pol1)
             else if(earlier(vars,y,x)) poly_ladd(vars, pol1,pol2)
             else {
               val e = poly_add(vars,c,d);
               val r = poly_add(vars,p,q);
               if(r == zero) e
               else Fn("+", List(e, Fn("*", List(Var(x), r))))
             }
      case (_,Fn("+",_)) => poly_ladd(vars,pol1,pol2)
      case (Fn("+",_),_) => poly_ladd(vars,pol2,pol1)
      case (Num(n),Num(m)) => Num(n + m)
      case _ =>   zero
    }
  
  def poly_ladd(vars: List[String], pol1: Term, pol2: Term): Term = 
    pol2 match {
      case (Fn("+",List(d,Fn("*",List(Var(y),q))))) =>
        Fn("+",List(poly_add(vars, pol1, d), Fn("*", List(Var(y), q))))
      case _ => throw new Error("poly_ladd: malformed input")
    }

  def poly_neg(q: Term): Term = q match {
    case Fn("+",List(c,Fn("*",List(Var(x),p)))) =>
      Fn("+",List(poly_neg(c), Fn("*",List(Var(x), poly_neg(p)))))
    case Num(n) => Num(-n)
    case _ => throw new Error("impossible")
  }

  def poly_sub(vars: List[String], p: Term, q: Term): Term = {
    val q1 = poly_neg(q);
    val r =poly_add(vars, p, poly_neg(q));
    r
  }

  def poly_mul(vars: List[String], pol1: Term, pol2: Term): Term = 
    (pol1,pol2) match {
     case (Fn("+", List(c, Fn("*",List(Var(x),p)))),
           Fn("+", List(d, Fn("*",List(Var(y),q))))) =>
             if(earlier(vars,x,y)) poly_lmul(vars, pol2, pol1)
             else poly_lmul(vars, pol1, pol2)
      case (Num(n), _) if n.is_zero => zero
      case (_,Num(n)) if n.is_zero => zero
      case (_,Fn("+",_)) => poly_lmul(vars,pol1,pol2)
      case (Fn("+",_),_) => poly_lmul(vars,pol2,pol1)
      case (Num(n),Num(m)) => Num(n * m)
      case _ => zero
    }
  def poly_lmul(vars: List[String], pol1: Term, pol2: Term): Term = 
    pol2 match {
      case (Fn("+",List(d,Fn("*",List(Var(y),q))))) =>
        poly_add(vars, poly_mul(vars, pol1, d),
                 Fn("+",List(zero,
                             Fn("*",List(Var(y), poly_mul(vars,pol1,q))))))
      case _ => throw new Error("poly_lmul: malformed input")
    }

  def funpow[A](n: Int, f: A => A, x: A): A = {
    if( n < 1 ) x
    else funpow(n-1, f, f(x))
  }


  def poly_pow(vars: List[String], p: Term, n: Int): Term = {
    funpow(n, (q:Term) => poly_mul(vars,p,q), one)
  }

/* I don't think we need this.
  def poly_div(vars: List[String], p: Term, q: Term) = q match {
    case Num(n) =>  poly_mul(vars, p, Num(1.0/n) ... ?

*/

  def poly_var(x: String): Term = {
    Fn("+",List(zero,Fn("*",List(Var(x), one))))
  }


  /* Put tm into canonical form.
   */
  def polynate(vars: List[String], tm: Term): Term = tm match {
    case Var(x) => poly_var(x)
    case Fn("-", t::Nil) => poly_neg(polynate(vars,t))
    case Fn("+", List(s,t)) => poly_add(vars,polynate(vars,s),
					polynate(vars,t))
    case Fn("-", List(s,t)) => poly_sub(vars,polynate(vars,s),
					polynate(vars,t))
    case Fn("*", List(s,t)) => poly_mul(vars,polynate(vars,s),
					polynate(vars,t))
    
    case Fn("/", List(Num(n),Num(m))) => Num(n / m)
    
    case Fn("^", List(p,Num(n))) => 
      poly_pow(vars,polynate(vars,p),n.intValue) //n is a Rational.
    case Num(n) => tm
    case _ => throw new Error("Unknown term: " + tm)
  }


  def polyatom(vars: List[String], fm: Formula): Formula = fm match {
    case Atom(R(a,List(s,t))) =>
      val r = Atom(R(a,List(polynate(vars,Fn("-",List(s,t))),zero)));
      r
    case _ => throw new Error("polyatom: not an atom.")
  }



  def coefficients(vars: List[String], p: Term): List[Term] = p match {
    case Fn("+", List(c, Fn("*", List(Var(x), q)))) if x == vars.head =>
      c::(coefficients(vars,q))
    case _ => List(p)
  }

  def degree(vars: List[String], p: Term): Int = {
    (coefficients(vars,p).length - 1)
  }

  def is_constant(vars: List[String], p: Term): Boolean = {
    degree(vars,p) == 0
  }
  
  def head(vars: List[String], p: Term): Term = {
    coefficients(vars,p).last
  }

  def behead(vars: List[String], tm: Term): Term = tm match {
    case Fn("+",List(c,Fn("*",List(Var(x),p)))) if x == vars.head =>
      val p1 = behead(vars,p);
      if(p1 == zero) c else Fn("+",List(c,Fn("*",List(Var(x),p1))))
    case _ => zero
  }

  def poly_cmul(k: Exact.Num, p: Term): Term = p match {
    case Fn("+", List(c, Fn("*", List( Var(x), q)))) =>
      Fn("+", List(poly_cmul(k,c),
                   Fn("*",List(Var(x),
                               poly_cmul(k,q)))))
    case Num(n) => Num(n * k)
    case _ => throw new Error("poly_cmul: non-canonical term" + p)
  }

  def headconst(p: Term): Exact.Num = p match {
    case Fn("+",List(c,Fn("*",List(Var(x),q)))) => headconst(q)
    case Num(n) => n
    case _ => throw new Error("headconst: malformed polynomial")
  }


  def monic(p: Term): (Term,Boolean) = {
    val h = headconst(p);
    if(h.is_zero) (p,false)
    else (poly_cmul(rOne / h, p), h < rZero)
  }




  val pdivide: List[String] => Term => Term =>  (Int, Term) = {
    def shift1(x: String): Term => Term = p =>  Fn("+",List(zero,
                                                       Fn("*",List(Var(x),
                                                                   p))));
    def pdivide_aux(vars: List[String], 
                    a: Term, 
                    n: Int, 
                    p: Term,
                    k: Int,
                    s: Term): (Int, Term) = {
      if(s == zero) (k,s) else {
        val b = head(vars, s);
        val m = degree(vars, s);
        if(m < n) (k,s) else {
          val p_1 = funpow(m-n, shift1(vars.head), p);
          if(a == b) pdivide_aux(vars,a,n,p,k,poly_sub(vars,s,p_1))
          else pdivide_aux(vars,a,n,p,k+1,
                           poly_sub(vars,poly_mul(vars,a,s),
                                    poly_mul(vars,b,p_1)))
        }
      }
    };
    vars => s => p => pdivide_aux(vars, head(vars,p), degree(vars,p), p, 0, s)
  }

  

  def poly_diffn(x: Term, n: Int, p: Term): Term = p match {
    case Fn("+", List(c, Fn("*", List(y,q)))) if y == x => 
      Fn("+", List(poly_cmul(new Exact.Rational(n), c), 
                   Fn("*", List(x, poly_diffn(x,n+1,q)))))
    case _ => poly_cmul( new Exact.Rational(n), p)
  }

  def poly_diff(vars: List[String], p: Term): Term = p match {
    case Fn("+", List(c, Fn("*", List(Var(x), q)))) if x == vars.head =>
      poly_diffn(Var(x), 1, q)
    case _ => zero
  }


/* End polynomical utilities.
 */


  def swap(swf: Boolean, s: Sign): Sign = {
    if(!swf) s else s match {
      case Positive() => Negative()
      case Negative() => Positive()
      case _ => s
    }
  }

  class FindSignFailure() extends Exception;

  def findsign(sgns: List[(Term,Sign)], p: Term): Sign = 
    try {
      val (p_1,swf) = monic(p);
      swap(swf,assoc(p_1,sgns))
    } catch {
      case e => throw new FindSignFailure()
    }

  def assertsign(sgns: List[(Term,Sign)], pr: (Term,Sign)): List[(Term,Sign)]
  = {
    val (p,s) = pr;
    if( p == zero ) {
      if(s == Zero()) sgns 
      else throw new Error("assertsign") }
    else {
    val (p_1,swf) = monic(p);
    val s_1 = swap(swf,s);
    val s_0 = try { assoc(p_1,sgns) } catch { case e => s_1};
    if(s_1 == s_0 || (s_0 == Nonzero() && (s_1==Positive() || s_1==Negative())))
      (p_1,s_1)::(sgns filterNot ( List((p_1,s_0)) contains ))
    else throw new Error("assertsign 1")
    }
  }

  final def split_zero(sgns: List[(Term,Sign)], pol: Term, 
                 cont_z: List[(Term,Sign)] => Formula,
                 cont_n: List[(Term,Sign)] => Formula) : Formula 
  = try {
      val z = findsign(sgns,pol);
      (if(z == Zero()) cont_z else cont_n)(sgns)
  } catch {
    case f: FindSignFailure => 
      val eq = Atom(R("=",List(pol,zero)));
      Binop(Or,Binop(And,eq, cont_z(assertsign(sgns, (pol,Zero())))),
         Binop(And,Not(eq), cont_n(assertsign(sgns,(pol,Nonzero())))))
  }


  val rel_signs = List(("=", List(Zero())),
                       ("<=", List(Zero(), Negative())),
                       (">=", List(Zero(), Positive())),
                       ("<", List(Negative())),
                       (">", List(Positive())) )





 def testform(pmat: List[(Term, Sign)], fm: Formula): Boolean = {
//   println("in testform. pmat = ");
//   pmat.map( x => {print("("); 
//                   P.printert(x._1); 
//                   println(", " + x._2 + ")");});
//   println("fm = ");
//   P.print_fol_formula(fm);
//   println();
    def f(r: Pred): Boolean = r match {
      case R(a,List(p,z)) => 
	mem(assoc(p, pmat), assoc(a, rel_signs))
      case _ => throw new Error("testform: bad Pred:" + r)
    };
    eval(fm, f)
  }


  def inferpsign(pr: (List[Sign], List[Sign])): List[Sign] = pr match {
    case (pd,qd) =>
      try {
        val i = index(Zero(), pd);
        el(i,qd)::pd
      } catch {
        case e:Failure => Nonzero() :: pd
      }
  }

  def condense(ps: List[List[Sign]]): List[List[Sign]] = ps match {
    case int::pt::other => 
      val rest = condense(other);
      if(mem(Zero(), pt)) int::pt::rest
      else rest
    case _ => ps
  }


  def inferisign(ps: List[List[Sign]]): List[List[Sign]] = ps match {
    case ((x@(l::ls))::(_::ints)::(pts@((r::rs)::xs))) =>
      (l,r) match {
        case (Zero(), Zero()) => throw new Error("inferisign: inconsistent")
        case (Nonzero() ,_) 
          |  (_, Nonzero()) => throw new Error("inferisign: indeterminate")
        case (Zero(),_) => x::(r::ints)::inferisign(pts)
        case (_,Zero()) => x::(l::ints)::inferisign(pts)
        case (Negative(), Negative()) 
          |  (Positive(), Positive()) =>  
            x::(l::ints)::inferisign(pts)
        case _ => x::(l::ints)::(Zero()::ints)::(r::ints)::inferisign(pts)
      }
    case _ => ps
  }



  def dedmatrix(cont: List[List[Sign]] => Formula,
                 mat: List[List[Sign]]) : Formula = {
    val l = (mat.head).length / 2;
    val mat1 = condense(mat.map((lst:List[Sign])=>inferpsign(lst.splitAt(l))));
//    val mat1 = condense(Parallel.pmap(mat,(lst:List[Sign])=>inferpsign(lst.splitAt(l))));
    val mat2 = List(swap(true, el(1,mat1.head)))::
                          (mat1 ++ List(List(el(1,mat1.last))));
    val mat3 = inferisign(mat2).tail.init;
    cont(condense(mat3.map((l:List[Sign]) => l.head :: l.tail.tail)))      
  }

  def pdivide_pos(vars: List[String], sgns: List[(Term,Sign)], 
                 s: Term, p: Term): Term
   = {
     val a = head(vars,p);
     val (k,r) = pdivide(vars)(s)(p);
     val sgn = findsign(sgns,a);
     if(sgn == Zero()) throw new Error("pdivide_pos: zero head coefficient.")
     else if(sgn == Positive() || (k % 2) == 0) r
     else if(sgn == Negative()) poly_neg(r)
     else poly_mul(vars,a,r)
   }

  def split_sign(sgns: List[(Term,Sign)], pol: Term, 
                 cont: List[(Term,Sign)] => Formula) : Formula = 
    findsign(sgns, pol) match {
      case Nonzero() => 
        val fm = Atom(R(">",List(pol,zero)));
        Binop(Or,Binop(And,fm,cont(assertsign(sgns,(pol,Positive())))),
           Binop(And,Not(fm),cont(assertsign(sgns,(pol,Negative())))))
      case _ => cont(sgns)
    }

  final def split_trichotomy(sgns: List[(Term,Sign)], 
                       pol: Term,
                       cont_z: List[(Term,Sign)] => Formula,
                       cont_pn: List[(Term,Sign)] => Formula) : Formula =
    split_zero(sgns,pol,cont_z,(s_1 => split_sign(s_1,pol,cont_pn)))


/* inlined
  final def monicize(vars: List[String], 
                     pols: List[Term],
                     cont: List[List[Sign]] => Formula,
                     sgns: List[(Term,Sign)] ): Formula = {
     val (mols,swaps) = List.unzip(pols.map(monic));
     val sols = setify(mols);
     val indices = mols.map(p => index(p, sols));
     def transform(m: List[Sign]) : List[Sign] = {
       (swaps zip indices).map( pr => swap(pr._1, el(pr._2, m)))}
     val (cont_1 : (List[List[Sign]] => Formula)) = mat => cont(mat.map(transform));
     matrix(vars,sols,cont_1,sgns)
     }
*/


  final def casesplit(vars: List[String],
                dun: List[Term],
                pols: List[Term],
                cont: List[List[Sign]] => Formula):
                List[(Term,Sign)]  => Formula = sgns => pols match {
//    case Nil => monicize(vars,dun,cont,sgns)
//    case Nil => matrix(vars,dun,cont,sgns)
    case Nil => val (mols,swaps) = dun.map(monic).unzip;
                val sols = setify(mols);
                val indices = mols.map(p => index(p, sols));
                def transform(m: List[Sign]) : List[Sign] = {
                  (swaps zip indices).map( pr => swap(pr._1, el(pr._2, m)))}
                val (cont_1 : (List[List[Sign]] => Formula)) = mat => cont(mat.map(transform));
                matrix(vars,sols,cont_1,sgns)
    case p::ops => 
      split_trichotomy(sgns,head(vars,p),
                       (if(is_constant(vars,p)) delconst(vars,dun,p,ops,cont)
                        else casesplit(vars,dun,behead(vars,p)::ops,cont)),
                       (if(is_constant(vars,p)) delconst(vars,dun,p,ops,cont)
                        else casesplit(vars,dun++List(p),ops,cont)))
  }

  final def delconst(vars: List[String], 
               dun: List[Term], 
               p: Term, 
               ops: List[Term],
               cont: List[List[Sign]] => Formula) :
               List[(Term,Sign)] => Formula = sgns => {
    def cont_1(m: List[List[Sign]]): Formula = 
      cont(m.map((rw:List[Sign]) => insertat(dun.length,findsign(sgns,p),rw)));
    casesplit(vars,dun,ops,cont_1)(sgns)
  }



  final def matrix(vars: List[String],
             pols: List[Term],
             cont: List[List[Sign]] => Formula,
             sgns: List[(Term,Sign)]): Formula = {
//    CV.lock.synchronized{
      if(CV.keepGoing == false) throw new CHAbort();
//    }

    if(pols == Nil) try { cont(List(Nil)) } catch {case e => False} else {
    /* find the polynomial of highest degree */
    val (p,_) = pols.foldLeft[(Term,Int)](zero,-1)(
      (bst:(Term,Int),ths:Term) => {val (p_1,n_1) = bst; 
                                    val n_2 =  degree(vars, ths);
                                    if(n_2 > n_1) (ths,n_2) else bst});
    val p_1 = poly_diff(vars,p);
    val i = index(p,pols);
    val qs = {val (p1,p2) = pols.splitAt(i);
              p_1::p1 ++ p2.tail};
//    println("in matrix. number of divisions to perform = " + qs.length);
    val gs = qs.map((p_3:Term) => pdivide_pos(vars,sgns,p,p_3));
//    val gs = Parallel.pmap(qs,((p_3:Term) => pdivide_pos(vars,sgns,p,p_3)));
    def cont_1(m: List[List[Sign]]): Formula = 
      cont(m.map(l => insertat(i,l.head,l.tail)));
    casesplit(vars, Nil, qs ++ gs, ls => dedmatrix(cont_1,ls))(sgns)
                                      
    }
  }

  val init_sgns:List[(Term,Sign)] = List((one, Positive()),
                                         (zero, Zero()));

  def basic_real_qelim(vars: List[String]): Formula => Formula 
  = fm => fm match {
    case Exists(x,p) =>
      val pols = atom_union(
        fm1 => fm1 match{case R(a,List(t,Num(n))) if n.is_zero => List(t)
                         case _ => Nil},
        p);
      val cont = (mat:List[List[Sign]]) => 
        if(mat.exists(m => testform(pols.zip(m),p))) True else False;
      casesplit(x::vars, Nil, pols, cont)(init_sgns)
    case _ => 
      throw new Error("impossible")
  }



  def real_elim(fm: Formula): Formula = {
    simplify(evalc(lift_qelim(polyatom,
                              fm1 => simplify(evalc(fm1)),
                              basic_real_qelim)(fm)))
  }


  /* better version that first converts to dnf */
  def real_elim2(fm: Formula): Formula = {
    simplify(evalc(lift_qelim(polyatom,
                              fm1 => dnf(cnnf( (x:Formula)=>x)(evalc(fm1))),
                              basic_real_qelim)(fm)))
  }

  def univ_close(fm: Formula): Formula = {
    val fvs = fv(fm);
    fvs.foldRight(fm) ((v,fm1) => Forall(v,fm1))
  }


  def unaryFns_Term(tm : Term): List[String] = tm match {
    case Fn(f, Nil) => List(f)
    case Fn(f, args) => 
      args.map(unaryFns_Term).flatten.distinct
    case _ => Nil
  }
  
  def unaryFns_Pred(fol: Pred) : List[String] = fol match {
    case R(r, args) => 
      args.map(unaryFns_Term).flatten.distinct
  }

  def replaceUnaryFns_Term(tm : Term): Term = tm match {
    case Fn(f, Nil) => Var(f)
    case Fn(f, args) => Fn(f, args.map(replaceUnaryFns_Term))
    case _ => tm
  }
  
  def replaceUnaryFns_Pred(fol: Pred) : Pred = fol match {
    case R(r, args) => 
      R(r,args.map(replaceUnaryFns_Term))
  }

  // free variables are existentially quantified.
  def makeQEable(fm : Formula) : Formula = {
    val fvs = fv(fm);
    val unary_fns = overatoms(fol => (lst: List[String]) 
                                 => unaryFns_Pred(fol)++lst  ,
                                  fm,Nil).distinct
    // XXX should uniqify
    val fm0 = onatoms(
      fol => Atom(replaceUnaryFns_Pred(fol)),fm)
    val fm1 = unary_fns.foldRight(fm0)((v,f) => Forall(v,f))
    fvs.foldRight(fm1) ((v,f) => Exists(v,f))
  }


  def real_elim_goal(fm: Formula): Boolean = {
    val fm0 = real_elim(fm);
    fm0 match {
      case True => true
      case _ => false
    }
  }


  def real_elim_goal_univ_closure(fm: Formula): Boolean = {
    val fm0 = real_elim(univ_close(fm));
    fm0 match {
      case True => true
      case _ => false
    }
  }
  


  @throws(classOf[CHAbort])
  def real_elim_try_universal_closure(fm: Formula, opt: Int): Formula = {
    val re = if(opt == 1) real_elim _ else real_elim2 _ ;
    val fm0 = simplify(evalc(fm));
//    println("after initial simplification:");
//    P.print_fol_formula(fm0);
    println();
    val fm1 =  re(fm0);
    if(fv(fm1).length < fv(fm).length || fv(fm).length == 0 )
      fm1
      else {
        println("; trying universal closure");
        val fm2 = re(univ_close(fm0));
        if(fm2 == True) True else fm1
      }

  }
  

  def elim_fractional_literals(fm: Formula): Formula = {
    def elim_fraction_term : Term => Term = tm => tm match {
      case Num(Exact.Rational(p,q)) => 
        if(p == BigInt(0)) Num(Exact.Integer(0))
        else if (q == BigInt(1)) Num(Exact.Integer(p))
	else  Fn("/", List(Num(Exact.Integer(p)), Num(Exact.Integer(q))))
      case Fn(f,args) => Fn(f, args.map(elim_fraction_term))
      case _ => tm
    }
    def elim_fraction_atom : Pred => Formula = fol => fol match {
      case R(s, List(t1,t2)) => 
        Atom(R(s, List(elim_fraction_term(t1),elim_fraction_term(t2))))
      case _ => Atom(fol)
    }
    onatoms(elim_fraction_atom, fm)
  }




  def test = poly_pow(List(), 
                      Fn("+",List(one, Fn("*",List(Var("x"), one)))),5);
//  def test1 = polynate(List("x"), P.parset("1 + x"));


  def test_qelim(func: Int, fm: Formula): Unit = {
    println("testing qelim on: ")
//    P.print_fol_formula(fm);
    println();
    val fm1 = if(func == 0) real_elim(fm) else real_elim2(fm);
    println("\nresult of qelim: ");
//    P.print_fol_formula(fm1);
//    println("\n here's a simplified verion:");
//    P.print_fol_formula(simplify_terms(fm1));
    println("\n-------------------");
  }


//  def test_qelim_s(func: Int, s:String): Unit = {
//    test_qelim(func, P.parse(s));
//  }


}




  

  


