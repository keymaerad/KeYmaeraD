package DLBanyan


import scala.text._
import scala.text.Document._


object Printing {

  val osw = new java.io.OutputStreamWriter(System.out)

  def printSequent(sq: Sequent): Unit = {
    val d = docOfSequent(sq)
    d.format(70, osw)
    osw.flush
  }


  def stringOfSequent(sq: Sequent): String = {
    val sw = new java.io.StringWriter()
    val d = docOfSequent(sq)
    d.format(70, sw)
    sw.toString
  }

  def stringOfFormula(fm: Formula): String = {
    val sw = new java.io.StringWriter()
    val d = docOfFormula(fm)
    d.format(70, sw)
    sw.toString
  }





  def docOfList(lst:List[Document], sep: Document) : Document = lst match {
    case Nil => DocNil
    case x:: Nil => x
    case x::xs => x :: sep ::  docOfList(xs,sep)
  }

  
  def bracket(b1:String, b2: String, d: Document): Document = {
    text(b1) :: DocNest(b1.length, d) :: text(b2)
  }

  def bracketp(b: Boolean)(b1:String, b2: String, d: Document): Document = {
    if(b)  bracket(b1,b2,d) else    DocNest(b1.length, d) ;
  }


  def docOfTermAux(pr:Int)(tm: Term): Document = tm match {
    case Var(x) =>
      Document.text(x)
    case Fn(f, List(x,y)) if List("+","-").contains(f) =>
      val pr1 = 2;
      bracketp(pr > pr1)("(",")", 
                         docOfTermAux(pr1)(x) ::text(f):: docOfTermAux(pr1+1)(y))
    case Fn(f, List(x,y)) if List("*","/").contains(f) =>
      val pr1 = 4;
      bracketp(pr > pr1)("(",")", 
                         docOfTermAux(pr1)(x) ::text(f):: docOfTermAux(pr1+1)(y))
    case Fn("-", List(x)) =>
     val pr1 = 6;
      "-" :: bracketp(pr > pr1)("(",")", 
                               docOfTermAux(pr1)(x))
    case Fn(f, List(x,y)) if List("^").contains(f) =>
      val pr1 = 8;
      bracketp(pr > pr1)("(",")", 
                         docOfTermAux(pr1)(x) ::text(f):: docOfTermAux(pr1+1)(y))
    case Fn(f,args) =>
      bracket(f+"(",")",
        docOfList(args.map(docOfTerm), text(",") :: DocBreak))
    case Num(n) =>
      Document.text(n.toString)
  }

  def docOfTerm(tm: Term): Document = 
    docOfTermAux(0)(tm)



  def docOfPred(p: Pred): Document = p match {
    case R(r,List(t1,t2)) if List("=", "<", ">", "<=", ">=", "<>"). contains(r) =>
      docOfTerm(t1) :: text(r) :: docOfTerm(t2)
    case R(r, ts)  =>
      bracket(r+"(",")",
        docOfList(ts.map(docOfTerm), text(",") :: DocBreak))
  }


  def docOfFormula(fm: Formula): Document = 
    docOfFormulaAux(0)(fm)

  def docOfFormulaAux(pr:Int)(fm: Formula): Document = fm match {
    case True => text("true")
    case False => text("false")
    case Not(fm) => 
      val pr1 = 12;
      text("~") :: docOfFormulaAux(pr1)(fm)
    case Atom(p) => docOfPred(p)
    case And(fm1,fm2) => 
      val pr1 = 10;
      bracketp(pr>pr1)("(",")", 
                       docOfFormulaAux(pr1)(fm1) :: text("&") :: 
                       docOfFormulaAux(pr1+1)(fm2))
    case Or(fm1,fm2) => 
      val pr1 = 8;
      bracketp(pr>pr1)("(",")",
                       docOfFormulaAux(pr1)(fm1) :: text("|") :: 
                       docOfFormulaAux(pr1+1)(fm2) )
    case Imp(fm1,fm2) =>
      val pr1 = 6;
      bracketp(pr>pr1)("(",")", 
                       docOfFormulaAux(pr1)(fm1) :: text("==>") :: 
                       docOfFormulaAux(pr1+1)(fm2))
    case Iff(fm1,fm2) => 
      val pr1 = 4;
      bracketp(pr>pr1)("(",")",
                       docOfFormulaAux(pr1)(fm1) :: text("<=>") :: 
                       docOfFormulaAux(pr1+1)(fm2))
    case Forall(x, fm) =>
      val pr1 = 2;
      bracketp(pr>pr1)("(",")",
                       text("forall ") :: text(x) ::
                       text(".") ::
                       docOfFormulaAux(pr1)(fm))
    case Exists(x,fm) => 
      val pr1 = 2;
      bracketp(pr>pr1)("(",")",
                       text("exists ") :: text(x) :: 
                       text(".") ::
                       docOfFormulaAux(pr1)(fm))
    case ForallOfSort(x,c, fm) =>
      val pr1 = 2;
      bracketp(pr>pr1)("(",")",
                       text("forall ") :: text(x) ::
                       text(":") :: docOfSort(c) ::
                       text(".") ::
                       docOfFormulaAux(pr1)(fm))
    case ExistsOfSort(x,c,fm) => 
      val pr1 = 2;
      bracketp(pr>pr1)("(",")",
                       text("exists ") :: text(x) :: 
                       text(":") :: docOfSort(c) :: 
                       text(".") ::
                       docOfFormulaAux(pr1)(fm))
    case Box(h,fm) =>
      val pr1 = 14;
      bracket("[","]", docOfHP(h)) :: docOfFormulaAux(pr1)(fm)
    case Diamond(h,fm) =>
      val pr1 = 14;
      bracket("<",">", docOfHP(h)) :: docOfFormulaAux(pr1)(fm)
  }


  def docOfHP(h: HP) : Document = h match {
    case Assign(f,tm) => 
     docOfTerm(f) :: text(":=") :: docOfTerm(tm)
    case AssignAny(x) =>
     docOfTerm(x) :: text(":= *")
    case AssignQuantified(i, c, f, theta) =>
      text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
          docOfTerm(f) :: text(":=") :: docOfTerm(theta)
    case Check(fm) =>
      text("?") :: docOfFormula(fm)
    case Seq(h1,h2) =>
      docOfHP(h1) :: text(";") :/: docOfHP(h2)
    case Choose(h1,h2) =>
      bracket("(",")", docOfHP(h1)) ::
          text(" ++") :/: 
          bracket("(",")",docOfHP(h2))
    case Loop(h, inv, hnts) =>
      bracket("{","}", docOfHP(h)):: text("*")
    case Evolve(derivs, reg, hnts, sols) =>
      bracket("{","}",
       docOfList(derivs.map(docOfDeriv), text(",")) ::
       text(";") ::
       docOfFormula(reg))
    case EvolveQuantified(i, c, f,v,h) =>
      text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
          docOfTerm(f) :: text("' =") :: docOfTerm(v) :: text("&") :: docOfFormula(h)
  }

  def docOfSort(c: Sort) : Document = c match {
    case St(n) => text(n)
    case Real => text("Real")
  }
  
  def docOfDeriv(pr: (Fn,Term )) : Document = {
    docOfTerm(pr._1) :: text("'") :: text(" = ") :: docOfTerm(pr._2)
  }

  def docOfSequent(sq: Sequent) : Document = sq match {
    case Sequent(c,s) =>
      docOfList(c.map(docOfFormula), DocCons(text(","), DocBreak)) :/:
       text("|-") :: DocNest(2,
        docOfList(s.map(docOfFormula), DocCons(text(","), DocBreak)))
  }


  def assoc[A,B](k: A, al: List[(A,B)]): Option[B] = al match {
    case (a,b) :: rest =>
      if( k == a ) Some(b)
      else assoc(k, rest)
    case Nil => None
  }

}

