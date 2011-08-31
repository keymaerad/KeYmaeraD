
package DLBanyan
//package cohenhormander;

import java.io.BufferedWriter
import java.io.OutputStreamWriter
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.InputStream
import java.io.FileInputStream


import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.syntactical._
import scala.util.parsing.combinator._


class DLLexical extends StdLexical {
  override def identChar = letter | elem('_') | elem('\'')
}


class DLParser(ins : String) 
 extends StdTokenParsers { 
  type Tokens = StdLexical ; val lexical = new DLLexical
  lexical.delimiters ++= List(",", ";",":", "(", ")","[","]","{","}",
                             "=", "<", ">", ">=", "<=", "/=",
                              "+","-","*", "/", "^",
                             "++", ":=", "@", "?", "\'",
                             "&", "|", "<=>", "==>", "|-", ".", "~", "->"
                            ).iterator
 
   lexical.reserved ++= List("forall", "exists",
                             "true", "false",
                             "solution", "invariant"
                           ).iterator
/*
   val ins : String = ""

   def this(ins1: String) = {
     this()
     ins = ins1
   }
*/
   def this(in : InputStream) = {
     this({
     val br = new BufferedReader(new InputStreamReader(in))
     var ins1 = ""
     var ln = br.readLine()
     while (ln != null){
       println( ln)
       ins1 = ins1 + ln + "\n"
       ln = br.readLine()
     }
     println("input = " + ins1)
     ins1
     })
   }



   def term: Parser[Term] = 
     prod*("+" ^^^ {(x:Term, y:Term) => Fn("+", List(x,y))} 
         | "-" ^^^ {(x: Term, y: Term) => Fn("-", List(x,y))}) 
     
   def prod: Parser[Term] =
     factor*("*" ^^^ {(x: Term, y: Term) 
                             => Fn("*", List(x, y))}  
             | "/" ^^^ {(x: Term, y: Term) 
                                =>  Fn("/", List(x, y))}) | 
     "-" ~> prod ^^ { x => Fn("-", List(Num(Exact.zero),x))} 

   def factor: Parser[Term] = 
      atomicTerm ~ "^" ~ numericLit ^^ 
             {case x ~ "^" ~ y => 
                  Fn("^", List(x,Num(Exact.Integer(Integer.parseInt(y)))))} |
      atomicTerm

   def function : Parser [Fn] = 
      (ident <~ "(") ~ ( repsep(term, ",") <~ ")") ^^
        {case f ~ xs => Fn(f, xs)} 


   def atomicTerm : Parser[Term] = 
      "(" ~> term <~  ")" | 
     numericLit ^^ (x => Num(Exact.Integer(Integer.parseInt(x)))) | 
     function | 
     ident ^^ (x => Var(x))


   def pred : Parser[Pred] = 
     term ~ ("=" | "/=" | "<" | ">" | "<=" | ">=" ) ~ term ^^
       { case t1 ~ r ~ t2 =>
          R(r, List(t1,t2))}


   def formula00 : Parser[Formula] = 
     "forall" ~> ident ~ "."~ formula00 ^^ 
               { case x ~ "." ~ f => Quantifier(Forall,Real,x, f)} |
     "exists" ~> ident ~ "."~ formula00 ^^ 
               { case x ~ "." ~ f => Quantifier(Exists,Real,x, f)} |
     "forall" ~> ident ~ ":" ~ ident ~ "." ~ formula00 ^^ 
               { case x ~ ":" ~ c ~ "." ~ f => Quantifier(Forall,St(c), x, f)} |
     "exists" ~> ident ~ ":" ~ ident ~ "." ~ formula00 ^^ 
               { case x ~ ":" ~ c ~ "." ~ f => Quantifier(Exists,St(c),x, f)} |
     formula0

   def formula0 : Parser[Formula] = 
     formula1*( "<=>" ^^^ {(f1:Formula,f2:Formula) => Binop(Iff,f1,f2)})

   // Implication is right-associative.
   def formula1 : Parser[Formula] = 
      rep1sep(formula2, "==>") ^^ 
        ((lst) => lst.reduceRight((f1:Formula,f2:Formula) => Binop(Imp,f1,f2)))

   def formula2 : Parser[Formula] = 
     formula3*( "|" ^^^ {(f1:Formula,f2:Formula) => Binop(Or,f1,f2)})

   def formula3 : Parser[Formula] = 
     formula4*( "&" ^^^ {(f1:Formula,f2:Formula) => Binop(And,f1,f2)})

   def formula4 : Parser[Formula] = 
     "~" ~> formula5 ^^ {fm => Not(fm)} | 
     formula5

   def formula5 : Parser[Formula] = 
     "(" ~> formula00 <~  ")" | 
     pred ^^ (x => Atom(x))  |
     "true" ^^^ True |
     "false" ^^^ False |
     // XXX doesn't work right for e.g. "[hp] forall x . ..."
     ("[" ~> hp <~ "]") ~ formula4 ^^ {case a ~ f => Modality(Box,a,f)} |
     ("<" ~> hp <~ ">") ~ formula4 ^^ {case a ~ f => Modality(Diamond,a,f)} 


   /* Distinguish between logical variables
    * and (unary) function symbols.
    */

   def freeVarsAreFns_Term(bndVars : List[String], tm : Term) : Term 
     = tm match {
       case Var(x) if ! (bndVars.contains(x)) =>
         Fn(x,Nil)
       case Fn(f, ps) =>
         val fnew =  f //if(bndVars.contains(f) ) xnew else f
         Fn(fnew, ps.map(p => freeVarsAreFns_Term(bndVars, p)))
       case _ => tm
     }


   def freeVarsAreFns_HP(bndVars : List[String], hp: HP) : HP = hp match {
    case Assign(vs) =>
      val vs1 = vs.map(vt => {
        val f@Fn(_,_) = freeVarsAreFns_Term(bndVars, vt._1)
        (f, freeVarsAreFns_Term(bndVars,vt._2)) })
      Assign(vs1)
    case AssignAny(f) => 
      val f1@Fn(_,_) = freeVarsAreFns_Term(bndVars,f)
      AssignAny(f1)
    case AssignQuantified(i,c,vs) =>
      AssignQuantified(i,c, vs.map(replace_asgn(i::bndVars)))
    case AssignAnyQuantified(i,c,f) =>
      val f1@Fn(_,_) = freeVarsAreFns_Term(i::bndVars,f)
      AssignAnyQuantified(i,c,f1)
    case Check(fm) =>
      Check(freeVarsAreFns(bndVars,fm))
    case Seq(p,q) => 
      Seq(freeVarsAreFns_HP(bndVars,p), freeVarsAreFns_HP(bndVars,q))
    case Choose(p,q) => 
      Choose(freeVarsAreFns_HP(bndVars,p), freeVarsAreFns_HP(bndVars,q))
    case Loop(p,fm, inv_hints) =>
      Loop(freeVarsAreFns_HP(bndVars,p), 
           freeVarsAreFns(bndVars,fm), 
           inv_hints.map(f => freeVarsAreFns(bndVars,f)))
    case Evolve(derivs, fm, inv_hints, sols) =>
      Evolve(derivs.map( replace_asgn(bndVars)), 
             freeVarsAreFns(bndVars,fm),
             inv_hints.map(f => freeVarsAreFns(bndVars,f)),
             sols.map(f => freeVarsAreFns(bndVars,f)))
     case EvolveQuantified(i,c,vs,h, sols) =>
//       println("in freevars are fns. h = " + h);
      EvolveQuantified(i,
                       c, 
                       vs.map(replace_asgn(i::bndVars)), 
                       freeVarsAreFns(i::bndVars,h),
                       sols.map(f => freeVarsAreFns(i::bndVars,f)))
       
   }

   val replace_asgn: List[String] => ((Fn, Term)) => (Fn, Term) = 
     bndVars => vt => {
       val (v,t) = vt
       val t1 = freeVarsAreFns_Term(bndVars,t)
       val v1@Fn(_,_) = freeVarsAreFns_Term(bndVars,v)
       (v1,t1)
     }




   def freeVarsAreFns(bndVars : List[String], fm: Formula) : Formula 
     = fm match {
       case True | False => fm
       case Atom(R(r,ps)) => 
         Atom(R(r, ps.map(p => freeVarsAreFns_Term(bndVars, p))))
       case Not(f) => Not(freeVarsAreFns(bndVars, f))
       case Binop(c,f1,f2) => 
         Binop(c, freeVarsAreFns(bndVars, f1),freeVarsAreFns(bndVars, f2))
       case Quantifier(q,c,v,f) =>
         Quantifier(q,c,v, freeVarsAreFns(v :: bndVars, f))
       case Modality(m,hp,phi) =>
         Modality(m,freeVarsAreFns_HP(bndVars, hp), freeVarsAreFns(bndVars, phi))
     }


   def formula : Parser[Formula] = 
     formula00 ^^ {fm => freeVarsAreFns(Nil, fm) }


   def hp : Parser[HP] =
     hp1*(";" ^^^ {(p1,p2) => Seq(p1,p2)})

   def hp1 : Parser[HP] = 
     hp2*("++" ^^^ {(p1,p2) => Choose(p1,p2)})


   def hp2 : Parser[HP] = 
     "(" ~> hp <~  ")" | 
      "?" ~> formula00 ^^ { x => Check(x)}  |
      ident <~ ":=" <~ "*" ^^ { x  => AssignAny(Fn(x,Nil))} |
      function <~ ":=" <~ "*" ^^ { f  => AssignAny(f)} |
      (ident <~ ":=") ~ term ^^ {case x ~ t => Assign(List((Fn(x,Nil),t)))} |
      (function <~ ":=") ~ term ^^ {case f ~ t => Assign(List((f,t)))} |
      (("forall" ~> ident <~  ":") ~ 
       ident ~ function <~ ":=") ~ term ^^ 
        {case i ~ c ~ f ~ v => AssignQuantified(i,St(c),List((f,v)))} | 
      (("forall" ~> ident <~  ":") ~ 
       ident ~ function <~ ":=") ~ "*" ^^ 
        {case i ~ c ~ f ~ "*" => AssignAnyQuantified(i,St(c),f)} | 
      // { alpha }*
      ("{" ~> hp  <~ "}" <~ "*") ~ annotation("invariant") ^^ 
            { case x ~ invs => Loop(x, True, invs)} | 
      // {x' = theta, ...; h}
      ("{" ~> rep1sep(diffeq, ",") <~ ";")  ~ 
          (formula00 <~ "}") ~ annotation("invariant") ~ annotation("solution") ^^
            {case dvs ~ f ~ invs ~ sols => Evolve(dvs,f,invs,sols)}  |
      // forall i : C  f(v)' = theta & h 
   // XXX  TODO figure out how to read apostrophes in a sane way
       ("forall" ~> ident <~ ":") ~ ident ~ 
        ("{" ~> rep1sep(qdiffeq, ",") <~ ";") ~ (formula00 <~ "}") ~ annotation("solution") ^^
        { case i ~ c ~ vs  ~ h ~ sols => 
          EvolveQuantified(i,St(c),vs,h, sols) }
   
     


  def diffeq : Parser[(Fn,Term)] = 
    (ident <~  "=") ~ term ^?
      {case s  ~ tm  if s.endsWith("\'") 
        => (Fn(s.substring(0,s.length - 1), Nil), tm)}

  def qdiffeq : Parser[(Fn,Term)] = 
    (function ~ ident <~  "=") ~ term ^?
      {case f ~ "\'" ~ tm  => (f, tm)}


   
  def annotation(name: String) : Parser[List[Formula]] = 
    "@" ~> keyword(name) ~> "(" ~> repsep(formula00, ",") <~ ")" |
    success(Nil)
       

  def sort : Parser[Sort] = 
    ident ^^ {case "Real" => Real
              case s => St(s)}

  def functionsort : Parser[(String,(List[Sort],Sort))] = 
    (ident <~ ":" <~ "(") ~ (repsep(sort,",") <~ ")" <~ "->") ~ sort ^^
      {case f ~ args ~ rtn => (f,(args,rtn))}

  def functionsorts : Parser[Map[String,(List[Sort],Sort)]] = 
    "{" ~> repsep(functionsort, ",") <~ "}" ^^ 
       {case fnsrts => scala.collection.immutable.HashMap.empty ++ fnsrts }


   def sequent : Parser[Sequent] = 
     functionsorts ~ repsep(formula, ",") ~ ("|-" ~> repsep(formula,",")) ^^ 
        {case fns ~ c ~ s => Sequent(fns, c,s)}


   def result : Option[Sequent] = {
     val ls = new lexical.Scanner(ins);
     phrase(sequent)(ls) match {
       case Success(r,next) if next.atEnd => 
         println("success! ")
         println(r)
         Some(r)
       case Success(r,next)  => 
         println("failure! Leftover input. only parsed: " )
         println(r)
         None
       case f => 
//         println("failure!")
         println(f)
         None
     }

   }


   def fm_result : Option[Formula] = {
     // don't infer var / fn distinction
     phrase(formula00)(new lexical.Scanner(ins)) match {
       case Success(r,next) if next.atEnd => 
         Some(r)
       case Success(r,next)  => 
         println("failure! Left over input. only parsed: " )
         println(r)
         None
       case f => 
//         println("failure!")
         println(f)
         None
     }

   }


} 




object P {
  def openFile(f:String) : InputStream = {
    new FileInputStream(f)
  }


  def parseFormula(f:String) : Formula = {
    val dlp = new DLParser(f)
    dlp.fm_result match {
      case Some(fm) => fm
      case None => 
        println("could not read a formula from " + f)
        False
    }
  }

}


