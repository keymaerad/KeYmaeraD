package DLBanyan

object MathematicaUtil {
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
    List(("Reduce", "nsmet"), 
         ( "FindInstance", "nsmet" ),
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
  
 //--- printing

  def math_sym(s: String): Expr =
    new Expr(Expr.SYMBOL, s)

  def math_int(s: String): Expr =
    new Expr(Expr.INTEGER, s)

  def un_fun(f: String, arg: Expr): Expr = {
    new Expr(math_sym(f),
             List(arg).toArray)
  }

  def bin_fun(f: String, arg1: Expr, arg2: Expr): Expr = {
    new Expr(math_sym(f),
             List(arg1,arg2).toArray)
  }



  def mathematica_of_term(tm: Term): Expr = tm match {
    case Var(x) => math_sym(x)
    case Num(Exact.Integer(n)) => math_int(n.toString)
    case Num(Exact.Rational(p,q)) => bin_fun("Divide", 
                                       math_int(p.toString),
                                       math_int(q.toString))
    case Fn("^",List(tm1,tm2)) => 
      bin_fun("Power", 
              mathematica_of_term(tm1),
              mathematica_of_term(tm2))
    case Fn("/",List(tm1,tm2)) => 
      bin_fun("Divide", 
              mathematica_of_term(tm1),
              mathematica_of_term(tm2))
    case Fn("*",List(tm1,tm2)) => 
      bin_fun("Times", 
              mathematica_of_term(tm1),
              mathematica_of_term(tm2))
    case Fn("-",List(tm1,tm2)) => 
      bin_fun("Subtract", 
              mathematica_of_term(tm1),
              mathematica_of_term(tm2))
    case Fn("-",List(tm)) => 
      un_fun("Minus",  mathematica_of_term(tm))
    case Fn("+",List(tm1,tm2)) => 
      bin_fun("Plus", 
              mathematica_of_term(tm1),
              mathematica_of_term(tm2))
    case _ => throw new Error ("don't know how to mathematify " + tm)

    }


    def math_name(r:String): String = r match {
      case "=" => "Equal"
      case "<>" => "Unequal"
      case "<" => "Less"
      case "<=" => "LessEqual"
      case ">" => "Greater"
      case ">=" => "GreaterEqual"
    }


    def strip_quant: Formula => (List[String], Formula) = fm => fm match {
      case Quantifier(Forall,Real, x,yp@Quantifier(Forall,Real,y,p))=> 
        val (xs,q) = strip_quant(yp);
        (x::xs,q)
      case Quantifier(Exists,Real, x,yp@Quantifier(Exists,Real,y,p))=> 
        val (xs,q) = strip_quant(yp);
        (x::xs,q)
      case Quantifier(Forall,Real,x,p) => (List(x),p)
      case Quantifier(Exists,Real,x,p) => (List(x),p)
      case _ => (Nil, fm)
    }

    def mathematica_of_formula(fm: Formula) :  Expr  = fm match {
      case False => math_sym("False")
      case True => math_sym("True")
      case Atom(R(r,List(lhs, rhs))) => 
        bin_fun(math_name(r), 
                mathematica_of_term(lhs),
                mathematica_of_term(rhs))
      case Atom(_) => throw new Error("non-binary relation")
      case Not(p) => 
        un_fun("Not", mathematica_of_formula(p))
      case Binop(And,p,q) => 
        bin_fun("And", mathematica_of_formula(p),mathematica_of_formula(q))
      case Binop(Or,p,q) => 
        bin_fun("Or", mathematica_of_formula(p),mathematica_of_formula(q))
      case Binop(Imp,p,q) => 
        bin_fun("Implies", mathematica_of_formula(p),
                           mathematica_of_formula(q))
      case Binop(Iff,p,q) => 
        bin_fun("Equivalent", mathematica_of_formula(p),
                              mathematica_of_formula(q))
      case Quantifier(Forall,Real,x,p) => 
        val (bvs, p1) = strip_quant(fm)
        val math_bvs = bvs.map(math_sym)
        bin_fun("ForAll", new Expr(math_sym("List"), math_bvs.toArray),
                          mathematica_of_formula(p1))
      case Quantifier(Exists,Real,x,p) => 
        val (bvs, p1) = strip_quant(fm)
        val math_bvs = bvs.map(math_sym)
        bin_fun("Exists", new Expr(math_sym("List"), math_bvs.toArray),
                          mathematica_of_formula(p1))
      case _ => throw new Error ("don't know how to mathematify " + fm)
    }
}
