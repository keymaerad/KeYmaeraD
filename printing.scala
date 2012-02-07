package KeYmaeraD


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
                         docOfTermAux(pr1)(x) ::text(" " + f + " "):: 
                         docOfTermAux(pr1+1)(y))
    case Fn(f, List(x,y)) if List("*","/").contains(f) =>
      val pr1 = 4;
      bracketp(pr > pr1)("(",")", 
                         docOfTermAux(pr1)(x) ::text(" " + f + " "):: 
                         docOfTermAux(pr1+1)(y))
    case Fn("-", List(x)) =>
     val pr1 = 6;
      "-" :: bracketp(pr > pr1)("(",")", 
                               docOfTermAux(pr1)(x))
    case Fn(f, List(x,y)) if List("^").contains(f) =>
      val pr1 = 8;
      bracketp(pr > pr1)("(",")", 
                         docOfTermAux(pr1)(x) ::text(f):: docOfTermAux(pr1+1)(y))
    case Fn(f,Nil) =>
      text(f+".")
    case Fn(f,args) =>
      bracket(f+"(",")",
        docOfList(args.map(docOfTerm), text(",") :: DocBreak))
    case Num(n) =>
      Document.text(n.toString)
  }

  def docOfTerm(tm: Term): Document = 
    docOfTermAux(0)(tm)



  def docOfPred(p: Pred): Document = p match {
    case R(r,List(t1,t2)) if List("=", "<", ">", "<=", ">=", "/="). contains(r) =>
      docOfTerm(t1) :: text(" " + r + " ") :: docOfTerm(t2)
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
    case Binop(And,fm1,fm2) => 
      val pr1 = 10;
      bracketp(pr>pr1)("(",")", 
                       docOfFormulaAux(pr1)(fm1) :: text(" & ") :: 
                       docOfFormulaAux(pr1+1)(fm2))
    case Binop(Or,fm1,fm2) => 
      val pr1 = 8;
      bracketp(pr>pr1)("(",")",
                       docOfFormulaAux(pr1)(fm1) :: text(" | ") :: 
                       docOfFormulaAux(pr1+1)(fm2) )
    // Implication is right-associative.
    case Binop(Imp,fm1,fm2) =>
      val pr1 = 6;
      bracketp(pr>pr1)("(",")", 
                       docOfFormulaAux(pr1+1)(fm1) :: text(" ==> ") :: 
                       docOfFormulaAux(pr1)(fm2))
    case Binop(Iff,fm1,fm2) => 
      val pr1 = 4;
      bracketp(pr>pr1)("(",")",
                       docOfFormulaAux(pr1)(fm1) :: text(" <=> ") :: 
                       docOfFormulaAux(pr1+1)(fm2))
    case Quantifier(qt, c,x, fm) =>
      val pr1 = 2;
      val dq = qt match { case Forall => text("forall ") 
                          case Exists => text("exists ") }
      bracketp(pr>pr1)("(",")",
                       dq :: text(x) ::
                       text(":") :: docOfSort(c) ::
                       text(".") ::
                       docOfFormulaAux(pr1)(fm))
    case Modality(Box, h,fm) =>
      val pr1 = 14;
      bracket("[","]", docOfHP(h)) :/: docOfFormulaAux(pr1)(fm)
    case Modality(Diamond, h,fm) =>
      val pr1 = 14;
      bracket("<",">", docOfHP(h)) :: docOfFormulaAux(pr1)(fm)
  }


  def docOfHP(h: HP) : Document = h match {
    case Assign(List((f,tm))) => 
     docOfTerm(f) :: text(" := ") :: docOfTerm(tm)
    case Assign(vs) => 
     bracket("{", "}", 
             docOfList(vs.map(v => docOfTerm(v._1)::text(" := ")::docOfTerm(v._2)), 
                                 text(",")))
    case AssignAny(x) =>
     docOfTerm(x) :: text(":= *")
    case AssignQuantified(i, c, List((f, theta))) =>
      text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
          docOfTerm(f) :: text(":=") :: docOfTerm(theta)
    case AssignAnyQuantified(i, c, f) =>
      text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
          docOfTerm(f) :: text(":= * ")
    case AssignQuantified(i,c,vs) => 
     text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
     bracket("{", "}", 
             docOfList(vs.map(v => docOfTerm(v._1)::text(":=")::docOfTerm(v._2)), 
                                 text(",")))
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
       docOfList(derivs.map(docOfDeriv), text(", ")) ::
       text(";") ::
       docOfFormula(reg))
    case EvolveQuantified(i, c, vs,reg,_) =>
      text("forall ") :: text(i) :: text(":") :: docOfSort(c) :: text(" ") ::
          bracket("{", "}",
                  docOfList(vs.map(docOfDeriv), text(", ")) ::
                    text(";") :: docOfFormula(reg))
  }

  def docOfSort(c: Sort) : Document = c match {
    case St(n) => text(n)
    case Real => text("Real")
    case AnySort => text("Any")
  }
  
  def docOfDeriv(pr: (Fn,Term )) : Document = {
    docOfTerm(pr._1) :: text("'") :: text(" = ") :: docOfTerm(pr._2)
  }

  def docOfSig1(sig1 : (String, (List[Sort], Sort))) : Document = {
    text(sig1._1) :: text(": (") :: 
    docOfList(sig1._2._1.map(docOfSort), text(", ")) ::
    text(") ->") :: docOfSort(sig1._2._2)
  }

  def docOfSig(sig : Map[String, (List[Sort], Sort)]) : Document = {
    text("{") :/:
    docOfList(sig.toList.map(docOfSig1), DocCons(text(", "), DocBreak)) :/:
    text("}") 
  }

  def docOfSequent(sq: Sequent) : Document = sq match {
    case Sequent(sig, c,s) => 
      docOfSig(sig) :/: 
      docOfList(c.map(docOfFormula), DocCons(text(", "), DocBreak)) :/:
       text("|-") :/: DocNest(2,
        docOfList(s.map(docOfFormula), DocCons(text(", "), DocBreak)))
  }


  def assoc[A,B](k: A, al: List[(A,B)]): Option[B] = al match {
    case (a,b) :: rest =>
      if( k == a ) Some(b)
      else assoc(k, rest)
    case Nil => None
  }

}

