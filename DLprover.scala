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


  // Can we apply quantifier elimination?
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
  def totalDeriv(d: List[(String,Term)], fm: Formula) : Formula 
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
    case Box(hp,phi) =>
      Box(rename_HP(xold,xnew,hp), rename_Formula(xold,xnew,phi))
    case Diamond(hp,phi) =>
      Diamond(rename_HP(xold,xnew,hp), rename_Formula(xold,xnew,phi))
    case _ => throw new Unimplemented()
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
      val replace_deriv: ((String, Term)) => (String, Term) = vt => {
        val (v,t) = vt
        val v1 =  if(v == xold) xnew else v
        val t1 = rename_Term(xold,xnew,t)
        (v1,t1)
      }
      Evolve(derivs.map( replace_deriv), 
             rename_Formula(xold,xnew,fm),
             inv_hints.map(f => rename_Formula(xold,xnew,f)),
             sols.map(f => rename_Formula(xold,xnew,f)))
      
  }

/*
  def rename_DLFormula(xold: String, 
                      xnew: String, 
                      dlfm: DLFormula): DLFormula = dlfm match {
    case NoModality(fm) =>
      NoModality(rename_Formula(xold, xnew, fm))
    case Box(hp, dlfm1) => 
      val hp1 = rename_HP(xold,xnew,hp)
      Box(hp1, rename_DLFormula(xold,xnew,dlfm1))
  }
*/

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
class ArithmeticNode(fm: Formula)
  extends DLNode() {

  def workHere(timeslice: Long): Unit = checkStatus() match {
    case Working() => 
       println("about to attempt quantifier elimination on:\n")
       P.print_Formula(fm)
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
           println("returned: " + P.string_of_Formula(r))
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
    "ArithmeticNode( " + P.string_of_Formula(fm)+ ")"
  } 

}


@serializable
class RedlogNode(fm: Formula)
  extends DLNode() {


  var mbe_process: Option[Process] = None

  val processLock = new Lock()


  def workHere(timeSlice: Long): Unit = checkStatus() match {
    case Working() => 
       println("about to attempt quantifier elimination on:\n")
       P.print_Formula(fm)
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
             println("returned: " + P.string_of_Formula(r))
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
    "RedlogNode( " + P.string_of_Formula(fm)+ ")"
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
class MathematicaNode(fm: Formula)
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
       P.print_Formula(fm)
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
    "MathematicaNode( " + P.string_of_Formula(fm)+ ")"
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
class ThreadedArithmeticNode( fm: Formula)
  extends DLNode() {

  var started = false

  val res = new Ref(None: Option[Boolean])

  val t = new Arithmetic(fm, res)

  var priority: Int = Thread.NORM_PRIORITY

  def workHere(timeSlice: Long): Unit = checkStatus() match {
    case Working() if !started =>
       println("about to attempt quantifier elimination on:\n")
       P.print_Formula(fm)
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
    "ArithmeticNode( " + P.string_of_Formula(fm)+ ")"
  } 

}

*/


