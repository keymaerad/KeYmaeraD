package KeYmaeraD


object Util {


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



  def allpairs[A,B](f: (A,A) => B, lst1: List[A], lst2: List[A]): List[B]
  = lst1 match {
    case e::es => lst2.map((a:A)=>f(e,a)) ++ allpairs(f,es,lst2)
    case Nil => Nil
  }




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

  implicit def connective2Ordered(c: Connective): Ordered[Connective] =
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
  // also: untested since some refactoring
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
        case Quantifier(Forall, x, Real, f) => that match {
          case False | True | Atom(_) | Not(_)
             | Binop(_,_,_) => 1
          case Quantifier(Forall, y, Real, g) =>
            val c = x compare y;
            if(c == 0) f compare g
            else c
          case _ => -1
        }
        case Quantifier(Exists, x, Real, f) => that match {
          case Quantifier(Exists, y, Real, g) =>
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
    case x::(rest@(y::_)) => x < y && setifiedp[A](rest)
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

  // Only deals with quantifiers over the reals.
  def nnf(fm: Formula): Formula = fm match {
    case Binop(And,p,q) => Binop(And,nnf(p), nnf(q))
    case Binop(Or,p,q) => Binop(Or,nnf(p), nnf(q))
    case Binop(Imp,p,q) => Binop(Or,nnf(Not(p)), nnf(q))
    case Binop(Iff,p,q) => Binop(Or, Binop(And, nnf(p), nnf(q)),
                                     Binop(And,nnf(Not(p)), nnf(Not(q))))
    case Not(Not(p)) => p
    case Not(True) => False
    case Not(False) => True
    case Not(Binop(And,p,q)) => Binop(Or,nnf(Not(p)),nnf(Not(q)))
    case Not(Binop(Or,p,q)) => Binop(And,nnf(Not(p)), nnf(Not(q)))
    case Not(Binop(Imp,p,q)) => Binop(And,nnf(p), nnf(Not(q)))
    case Not(Binop(Iff,p,q)) => Binop(Or,Binop(And,nnf(p),nnf(Not(q))),
                                      Binop(And,nnf(Not(p)),nnf(q)))
    case Quantifier(Forall, x, c, p) => Quantifier(Forall,x,c,nnf(p))
    case Quantifier(Exists, x, c, p) => Quantifier(Exists,x,c,nnf(p))
    case Not(Quantifier(Forall,x,c@Real,p)) => Quantifier(Exists,x,c,nnf(Not(p)))
    case Not(Quantifier(Exists,x,c@Real,p)) => Quantifier(Forall,x,c,nnf(Not(p)))
    case _ => fm
  }

  // There's gotta be a more efficient way.
  def prenex(fm : Formula): Formula = fm match {
    case True | False | Atom(_) => fm
    case Not(f1) =>
      prenex(f1) match {
        case Quantifier(Forall, i, srt, pf1) =>
          Quantifier(Exists, i, srt, prenex(Not(pf1)))
        case Quantifier(Exists, i, srt, pf1) =>
          Quantifier(Forall, i, srt, prenex(Not(pf1)))
        case _ => fm
      }
    case Binop(op, f1, f2) if op == And || op == Or =>
      prenex(f1) match {
        case Quantifier(qt, i, srt, pf1) =>
          Quantifier(qt, i, srt, prenex(Binop(op, pf1, f2)))
        case pf1 =>
          prenex(f2) match {
            case Quantifier(qt, i, srt, pf2) =>
              Quantifier(qt, i, srt, prenex(Binop(op, pf1, pf2)))
            case pf2 =>
              fm
          }
      }
    case Binop(Imp, f1, f2)  =>
      prenex(f1) match {
        case Quantifier(Forall, i, srt, pf1) =>
          Quantifier(Exists, i, srt, prenex(Binop(Imp, pf1, f2)))
        case Quantifier(Exists, i, srt, pf1) =>
          Quantifier(Forall, i, srt, prenex(Binop(Imp, pf1, f2)))
        case pf1 =>
          prenex(f2) match {
            case Quantifier(qt, i, srt, pf2) =>
              Quantifier(qt, i, srt, prenex(Binop(Imp, pf1, pf2)))
            case pf2 =>
              fm
          }
      }
    // TODO IFF
    case Quantifier(qt, i, srt, f1) =>
      Quantifier(qt, i, srt, prenex(f1))
    case _ => throw new Error("unsupported in prenex: " + fm)

  }

  def subFormulas(fm: Formula): List[Formula] = fm match {
    case False | True | Atom(_) => List(fm)
    case Not(p) => union(List(fm), subFormulas(p))
    case Binop(_,p,q) => union(List(fm), union(subFormulas(p), subFormulas(q)))
    case Quantifier(_,_,_,p) => union(List(fm), subFormulas(p))
    case Modality(_,_,p) => union(List(fm), subFormulas(p)) //may need to be modified!!!
    case _ =>
      throw new Error("nonfirstorder arithmetic")
  }



  def vari(fm: Formula): List[String] = fm match {
    case False | True => Nil
    case Atom(R(p,args)) => unions(args.map(fv_Term))
    case Not(p) => vari(p)
    case Binop(_,p,q) => union(vari(p), vari(q))
    case Quantifier(_,x,_,p) => insert(x, vari(p))
    case _ =>
      throw new Error("nonfirstorder arithmetic")
  }


  def fv_Term(tm: Term): List[String] = tm match {
    case Var(x) => List(x)
    case Fn(f,args) => unions(args.map(fv_Term))
    case Num(_) => Nil
  }

  def fv_HP(hp: HP) : List[String] = hp match {
    case Assign(vs) =>
      val fvs = vs.map(v => fv_Term(v._2))
      unions(fvs)
    case AssignAny(x) => Nil // XXX what about the arguments?
    case AssignQuantified(i,c,vs) =>
      unions(vs.map(v => union(fv_Term(v._1),fv_Term(v._2))))
    case AssignAnyQuantified(i,c,vs) =>
      Nil // XXX
    case Check(fm) =>
      fv(fm)
    case Seq(p,q) =>
      union(fv_HP(p), fv_HP(q))
    case Choose(p,q) =>
      union(fv_HP(p), fv_HP(q))
    case Loop(p,fm, inv_hints) =>
      union(fv_HP(p), fv(fm))
    case Evolve(derivs, fm, _, _) =>
      union(fv(fm),
            unions(derivs.map(v => union(fv_Term(v._1),fv_Term(v._2)))))
    case EvolveQuantified(i,c,vs,h, _ ) =>
      val fvs = union(fv(h),
                      unions(vs.map(v => union(fv_Term(v._1),fv_Term(v._2)))))
      subtract(fvs, List(i))
  }

  def fv(fm: Formula): List[String] = fm match {
    case False | True => Nil
    case Atom(R(p,args)) => unions(args.map(fv_Term))
    case Not(p) => fv(p)
    case Binop(_,p,q) => union(fv(p), fv(q))
    case Quantifier(_,x,_,p) => subtract(fv(p) ,List(x))
    case Modality(m, hp, p) => union(fv_HP(hp), fv(p))
    case _ =>
      throw new Error("nonfirstorder arithmetic")
  }



}
