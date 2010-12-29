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
                             "=", "<", ">", ">=", "<=", "<>",
                              "+","-","*", "/", "^",
                             "++", ":=", "@", "?", "\'",
                             "&", "|", "<=>", "==>", "|-", ".", "~"
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
       ins1 = ins1 + ln
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
     term ~ ("=" | "<" | ">" | "<=" | ">=" ) ~ term ^^
       { case t1 ~ r ~ t2 =>
          R(r, List(t1,t2))}


   def formula : Parser[Formula] = 
     "forall" ~> ident ~ "."~ formula ^^ { case x ~ "." ~ f => Forall(x,f)} |
     "exists" ~> ident ~ "."~ formula ^^ { case x ~ "." ~ f => Exists(x,f)} |
     formula0

   def formula0 : Parser[Formula] = 
     formula1*( "<=>" ^^^ {(f1,f2) => Iff(f1,f2)})

   // XXX This should be right-associative instead.
   def formula1 : Parser[Formula] = 
     formula2*( "==>" ^^^ {(f1,f2) => Imp(f1,f2)})

   def formula2 : Parser[Formula] = 
     formula3*( "|" ^^^ {(f1,f2) => Or(f1,f2)})

   def formula3 : Parser[Formula] = 
     formula4*( "&" ^^^ {(f1,f2) => And(f1,f2)})

   def formula4 : Parser[Formula] = 
     "~" ~> formula5 ^^ {fm => Not(fm)} | 
     formula5

   def formula5 : Parser[Formula] = 
     "(" ~> formula <~  ")" | 
     pred ^^ (x => Atom(x))  |
     "true" ^^^ True |
     "false" ^^^ False |
     ("[" ~> hp <~ "]") ~ formula4 ^^ {case a ~ f => Box(a,f)} |
     ("<" ~> hp <~ ">") ~ formula4 ^^ {case a ~ f => Diamond(a,f)} 


   def hp : Parser[HP] =
     hp1*(";" ^^^ {(p1,p2) => Seq(p1,p2)})

   def hp1 : Parser[HP] = 
     hp2*("++" ^^^ {(p1,p2) => Choose(p1,p2)})


   def hp2 : Parser[HP] = 
     "(" ~> hp <~  ")" | 
      "?" ~> formula ^^ { x => Check(x)}  |
      ident <~ ":=" <~ "*" ^^ { x  => AssignAny(x)} |
      (ident <~ ":=") ~ term ^^ {case x ~ t => Assign(x,t)} |
      // forall i : C f(v) := theta
      (("forall" ~> ident <~  ":") ~ 
       ident ~ function <~ ":=") ~ term ^^ 
        {case i ~ c ~ f ~ v => AssignQuantified(i,Tp(c),f,v)} | 
      // { alpha }*
      ("{" ~> hp  <~ "}" <~ "*") ~ annotation("invariant") ^^ 
            { case x ~ invs => Loop(x, True, invs)} | 
      // {x' = theta, ...; h}
      ("{" ~> rep1sep(diffeq, ",") <~ ";")  ~ 
          (formula <~ "}") ~ annotation("invariant") ~  annotation("solution") ^^
            {case dvs ~ f ~ invs ~ sols => Evolve(dvs,f,invs,sols)}  |
      // forall i : C  f(v)' = theta & h 
   // XXX  TODO figure out how to read apostrophes in a sane way
      ((("forall" ~> ident <~ ":") ~ ident ~ function ~ ident <~ "=")  ~
           term <~ "&")  ~ formula ^^
        { case i ~ c ~ f ~ "\'" ~ v ~ h => EvolveQuantified(i,Tp(c),f,v,h) }
   
     


  def diffeq : Parser[(String,Term)] = 
    (ident <~  "=") ~ term ^?
      {case s  ~ tm  if s.endsWith("\'") 
        => (s.substring(0,s.length - 1), tm)}
   
  def annotation(name: String) : Parser[List[Formula]] = 
    "@" ~> keyword(name) ~> "(" ~> repsep(formula, ",") <~ ")" |
    success(Nil)
       


   def sequent : Parser[Sequent] = 
     repsep(formula, ",") ~ ("|-" ~> repsep(formula,",")) ^^ 
        {case c ~ s => Sequent(c,s)}


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
     phrase(formula)(new lexical.Scanner(ins)) match {
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

}


