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


class DLParser(in: InputStream) 
 extends StdTokenParsers { 
  type Tokens = StdLexical ; val lexical = new DLLexical
  lexical.delimiters ++= List(",", ";", "(", ")","[","]","{","}",
                             "=", "<", ">", ">=", "<=", "<>",
                              "+","-","*", "/", "^",
                             "++", ":=", "@", "?", "\'",
                             "&", "|", "<=>", "==>", "|-", "."
                            ).iterator
 
   lexical.reserved ++= List("forall", "exists",
                             "true", "false",
                             "solution", "invariant"
                           ).iterator

   val br = new BufferedReader(new InputStreamReader(in))
   var ins = ""
   var ln = br.readLine()
   while (ln != null){
     println( ln)
     ins = ins + ln
     ln = br.readLine()
   }

   println("input = " + ins)

   def term: Parser[Term] = 
     prod*("+" ^^^ {(x:Term, y:Term) => Fn("+", List(x,y))} 
         | "-" ^^^ {(x: Term, y: Term) => Fn("-", List(x,y))}) 
     
   def prod: Parser[Term] =
     factor*("*" ^^^ {(x: Term, y: Term) 
                             => Fn("*", List(x, y))}  
             | "/" ^^^ {(x: Term, y: Term) 
                                =>  Fn("/", List(x, y))}) | 
     "-" ~> prod ^^ { x => Fn("*", List(Num(Exact.negone),x))} 

   def factor: Parser[Term] = 
      atomicTerm ~ "^" ~ numericLit ^^ 
             {case x ~ "^" ~ y => 
                  Fn("^", List(x,Num(Exact.Integer(Integer.parseInt(y)))))} |
      atomicTerm

   def atomicTerm : Parser[Term] = 
      "(" ~> term <~  ")" | 
     numericLit ^^ (x => Num(Exact.Integer(Integer.parseInt(x)))) | 
     (ident <~ "(") ~ ( repsep(term, ",") <~ ")") ^^
        {case f ~ xs => Fn(f, xs)} |
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

   def formula1 : Parser[Formula] = 
     formula2*( "==>" ^^^ {(f1,f2) => Imp(f1,f2)})

   def formula2 : Parser[Formula] = 
     formula3*( "|" ^^^ {(f1,f2) => Or(f1,f2)})

   def formula3 : Parser[Formula] = 
     formula4*( "&" ^^^ {(f1,f2) => And(f1,f2)})

   def formula4 : Parser[Formula] = 
     "(" ~> formula <~  ")" | 
     pred ^^ (x => Atom(x))  |
     "true" ^^^ True |
     "false" ^^^ False |
     ("[" ~> hp <~ "]") ~ formula4 ^^ {case a ~ f => Box(a,f)} |
     ("<" ~> hp <~ ">") ~ formula4 ^^ {case a ~ f => Diamond(a,f)} 


   def hp : Parser[HP] =
     hp1*("++" ^^^ {(p1,p2) => Choose(p1,p2)})

   def hp1 : Parser[HP] = 
     hp2*(";" ^^^ {(p1,p2) => Seq(p1,p2)})

   def hp2 : Parser[HP] = 
     "(" ~> hp <~  ")" | 
      "?" ~> formula ^^ { x => Check(x)}  |
      ident <~ ":=" <~ "*" ^^ { x  => AssignAny(x)} |
      (ident <~ ":=") ~ term ^^ {case x ~ t => Assign(x,t)} |
     ("{" ~> hp  <~ "}" <~ "*") ~ annotation("invariant") ^^ 
           { case x ~ invs => Loop(x, True, invs)} | 
//     "{" ~> hp  <~ "}" <~ "*" ^^ { x => Loop(x, True, Nil)} | 
     ("{" ~> rep1sep(diffeq, ",") <~ ";")  ~ 
         (formula <~ "}") ~ annotation("invariant") ~  annotation("solution") ^^
           {case dvs ~ f ~ invs ~ sols => Evolve(dvs,f,invs,sols)}


  def diffeq : Parser[(String,Term)] = 
    ident ~ "=" ~ term ^?
      {case s ~ "=" ~ tm if s.last == '\'' =>
        ((s.substring(0,s.length - 1), tm))}
   
  def annotation(name: String) : Parser[List[Formula]] = 
    "@" ~> keyword(name) ~> "(" ~> repsep(formula, ",") <~ ")" |
    success(Nil)
       


   def sequent : Parser[Sequent] = 
     repsep(formula, ",") ~ ("|-" ~> repsep(formula,",")) ^^ 
        {case c ~ s => Sequent(c,s)}



   def result : Option[Sequent] = {
     phrase(sequent)(new lexical.Scanner(ins)) match {
       case Success(r,next) if next.atEnd => 
         println("success! ")
         println(r)
         Some(r)
       case Success(r,next)  => 
         println("failure! Left over input. only parsed: " )
         println(r)
         None
       case f => 
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



/*
class ParseFailure(s: String, ast: Any, rest: Parser.Tokens ) extends Exception {
  override def toString() : String = {
    "ParseFailure: " + s + "\n parsed: " + ast + "\n rest: " + rest
   }
}


object Parser {
  type Token = String;
  type Tokens = List[String];

  def explode(s: String): List[Char] = 
    s.toCharArray().toList

  def matches(s: String): Char => Boolean = {
    (c: Char) => (s contains c)
  }

  def space = matches(" \t\n\r")
  def punctuation = matches("()[]{},")
  def symbolic = matches("~`!#$%^&*-+=|\\:;<>.?/")
  def numeric = matches("0123456789")
  def alphanumeric = matches(
    "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")

  def lexwhile(prop: Char => Boolean, inp: List[Char]): 
       (String, List[Char]) = inp match {
	 case (c::cs) if prop(c) => 
	   val (tok,rest) = lexwhile(prop, cs);
	   (c + tok, rest)
         case _ => ("", inp)
       }


  def lex(inp: List[Char]): List[String] = 
    (lexwhile(space, inp))._2  match {
      case Nil => Nil
      case (c::cs) => 
	val prop = if( alphanumeric(c))  alphanumeric
		   else if(symbolic(c))  symbolic
		   else ((c:Char) => false);
        val (toktl,rest) = lexwhile(prop, cs);
        (c + toktl):: (lex(rest))
    }


  def make_parser[A](pfn: List[String] => (A, List[String]), s: String):
    A = { 
      val (expr,rest) = pfn(lex(explode(s)));
      if(rest == Nil)
	expr
      else {
	throw new ParseFailure("unparsed input. ", expr, rest )
      }
    }




  def parse_ginfix[A,B](opsym: Token, 
                        opupdate: ((A => B),A) => 
                                   (A => B),
                   sof: A => B,
                   subparser: Tokens => (A,Tokens),
                   inp: Tokens): (B,Tokens) = {
      val (e1,inp1) = subparser(inp);
      if((inp1 != Nil) && inp1.head == opsym)
      parse_ginfix(opsym,opupdate,opupdate(sof,e1),subparser,inp1.tail)
      else (sof(e1),inp1)
  }
                     
  def parse_left_infix[A](opsym: Token, 
                       opcon: (A,A) => A,
                       subparser: Tokens => (A,Tokens)) :
                       Tokens =>  (A,Tokens) = {
   (inp:Tokens) => {
     parse_ginfix(opsym, 
                  (f:A => A,e1:A) => 
                   ((e2:A) => opcon(f(e1),e2)), 
                  (x:A) => x,
                  subparser, inp)
    }
  }

  def parse_right_infix[A](opsym: Token, 
                           opcon: (A,A) => A,
                           subparser: Tokens => (A,Tokens))
                           (inp:Tokens) : (A,Tokens) = 
    parse_ginfix(opsym, 
                 (f:A => A,e1:A) => 
                  ((e2:A) => f(opcon(e1,e2))), 
                 (x:A) => x,
                 subparser, inp)


  def parse_list[A](opsym: Token, 
                    subparser: Tokens => (A,Tokens)):
                    Tokens => (List[A],Tokens) = {
    (inp:Tokens) => {
      parse_ginfix(opsym, 
                   (f:A=>List[A],e1:A) => 
                     ((e2:A) => (f(e1) ++ List(e2))), 
                   (x:A) => List(x),
                   subparser, inp)
    }
  }

  
  def papply[A,B,C](f: A => B, pr: (A,C)): (B,C) = pr match {
    case (ast,rest) => (f(ast), rest)
  }

  def nextin(inp: Tokens, tok: String): Boolean = {
    (inp != Nil) && (inp.head == tok)
  }

  def parse_tok(tok: String, inp: Tokens ): Tokens = {
    if(nextin(inp,tok)) inp.tail
    else throw new ParseFailure("parse_tok: " + tok, (), inp)
  }

  def parse_bracketed[A](subparser: Tokens => (A,Tokens),
                         cbra: String,
                         inp: Tokens): (A, Tokens) = {
    val (ast,rest) = subparser(inp);
    if (nextin(rest,cbra)) (ast,rest.tail)
    else throw new 
    ParseFailure("\n Closing bracket " + cbra + " expected.", ast, rest)
  }



  def parse_atomic_formula(fns: ((Tokens,Tokens)=>(FOFormula,Tokens), 
                                 (Tokens,Tokens)=>(FOFormula,Tokens)),
                           vs: Tokens):
                           Tokens => (FOFormula,Tokens) = {
    (inp:Tokens) => {
      val (ifn,afn) = fns;
      inp match {
        case Nil => throw new ParseFailure("formula expected", (),inp)
        case "false"::rest => (False, rest)
        case "true"::rest => (True,rest)
        case "("::rest => 
              try { ifn(vs,inp) } catch { case p:ParseFailure =>
                parse_bracketed (inp => parse_formula(fns, vs, inp),
                                 ")", rest)
                                       }
        case "~"::rest => papply( (p:FOFormula) => Not(p), 
                                 parse_atomic_formula(fns,vs)(rest))
        case "forall"::x::rest =>
          parse_quant(fns, x::vs, 
                      ((y:Token,p:FOFormula) => Forall(y,p)), x, rest)
        case "exists"::x::rest =>
          parse_quant(fns, x::vs, 
                      ((y:Token,p:FOFormula) => Exists(y,p)), x, rest)
        case _ => afn(vs,inp)
      }
        
    }
  }
  
  def parse_quant(fns:  ((Tokens,Tokens)=>(FOFormula,Tokens), 
                         (Tokens,Tokens)=>(FOFormula,Tokens)),
                  vs: Tokens,
                  qcon: (Token,FOFormula) => FOFormula,
                  x: Token,
                  inp: Tokens): (FOFormula, Tokens) = inp match {
    case Nil => 
      throw new ParseFailure("Body of quantified term expected.",(), inp)
    case y :: rest =>
      papply((fm:FOFormula) => qcon(x,fm),
             if(y==".") parse_formula(fns,vs,rest)
             else parse_quant(fns,y::vs,qcon,y,rest))
  }



  def parse_formula(fns: ((Tokens,Tokens)=>(FOFormula,Tokens), 
                          (Tokens,Tokens)=>(FOFormula,Tokens)),
                    vs: Tokens,
                    inp: Tokens): (FOFormula,Tokens) = {
    parse_right_infix("<=>",  ((p:FOFormula,q:FOFormula) => Iff(p,q)),
      parse_right_infix("==>", ((p:FOFormula,q:FOFormula) => Imp(p,q)),
        parse_right_infix("|", ((p:FOFormula,q:FOFormula) => Or(p,q)),
          parse_right_infix("&", ((p:FOFormula,q:FOFormula) => And(p,q)),
            parse_atomic_formula(fns, vs)))))(inp)
  }


  def is_const_name(s: Token): Boolean = {
    (explode(s).forall(numeric)) //|| (s == "nil")
  }

  def parse_atomic_term(vs: Tokens): Tokens => (Term, Tokens) = {
    (inp:Tokens) => inp match {
      case Nil => throw new ParseFailure("term expected", (), inp)
      case "("::rest => parse_bracketed(parse_term(vs), ")", rest)
      case "-"::rest => papply ((t:Term) => Fn("-",List(t)),
                                parse_atomic_term(vs)(rest))
      case f::"("::")"::rest => (Fn(f,Nil),rest)
      case f::"("::rest =>
        papply ((args:List[Term]) => Fn(f,args),
                parse_bracketed(parse_list(",",parse_term(vs)),
                                ")",rest))
      case a::rest => 
        (if (is_const_name(a) && (! vs.contains(a))) Num(new Exact.Integer(a)) 
         else Var(a),
         rest)
    }
  }


  // "vs" is the list of bound variables.
  def parse_term(vs: Tokens): Tokens => (Term,Tokens) = {
    parse_right_infix("::",((e1:Term,e2:Term) => Fn("::",List(e1,e2))),
     parse_right_infix("+",((e1:Term,e2:Term) => Fn("+",List(e1,e2))),
      parse_left_infix("-",((e1:Term,e2:Term) => Fn("-",List(e1,e2))),
       parse_right_infix("*",((e1:Term,e2:Term) => Fn("*",List(e1,e2))),
        parse_left_infix("/",((e1:Term,e2:Term) => Fn("/",List(e1,e2))),
         parse_left_infix("^",((e1:Term,e2:Term) => Fn("^",List(e1,e2))),
          parse_atomic_term(vs)))))))
  }

  val parset = (inp: String) => make_parser(parse_term(Nil), inp);

  val comparators = List("=","<","<=",">",">=");

  def parse_infix_atom(vs: Tokens, inp: Tokens): (FOFormula, Tokens) = {
    val (tm,rest) = parse_term(vs)(inp);
    if(comparators.exists( x => nextin(rest,x)))
      papply((tm1:Term) => Atom(R(rest.head,List(tm,tm1))),
             parse_term(vs) (rest.tail))
    else throw new ParseFailure("parse_infix_atom", tm, rest)
  }

  def parse_atom(vs: Tokens, inp: Tokens): (FOFormula, Tokens) = {
    try {
      parse_infix_atom(vs,inp)
    } catch {
      case p:ParseFailure =>
        inp match {
          case p::"("::")"::rest => (Atom(R(p,Nil)),rest)
          case p::"("::rest =>
            papply ((args:List[Term]) => Atom(R(p,args)),
                    parse_bracketed(parse_list(",",parse_term(vs)),")",rest))
          case p::rest if p != "(" => (Atom(R(p,Nil)),rest)
          case _ => throw new ParseFailure("parse_atom", (), inp)
        }
    }
  }


  def parse_diffeq : Tokens => ((String, Term), Tokens) = inp => inp match {
    case s::"="::rest  if s.last == '\'' =>
      val (tm,rest1) = parse_term(Nil)(rest)
      ((s.substring(0,s.length - 1), tm), rest1)
    case _ => throw new ParseFailure("diffeq", (), inp)
  }

  def parse_evolve: Tokens => (HP, Tokens) = inp => inp match {
    case "{"::rest =>
      val (derivs,rest1) = parse_list(",", parse_diffeq)(rest)
        //parse_bracketed(parse_list(",", parse_diffeq), ";", rest)
      val rest2 = parse_tok(";", rest1 );
      val (fm, rest3) = parse_formula0(rest2)
      val rest4 = parse_tok("}", rest3)
      rest4 match {
        case "@" :: "invariant" :: rest5 =>
          val rest6 = parse_tok("(", rest5)
          val (invs,rest7) = parse_list(",",parse_formula0)(rest6)
          val rest8 = parse_tok(")", rest7)
          (Evolve(derivs, fm, invs, Nil), rest8)
        case "@" :: "solution" :: rest5 =>
          val rest6 = parse_tok("(", rest5)
          val (sols,rest7) = parse_list(",",parse_formula0)(rest6)
          val rest8 = parse_tok(")", rest7)
          (Evolve(derivs, fm, Nil, sols ), rest8)
        case _ =>
          (Evolve(derivs, fm, Nil, Nil), rest4)
      }
    case _ => throw new ParseFailure("evolve", (), inp)
      
  }

  def parse_repeat: Tokens => (HP, Tokens) = inp => inp match {
    case "{":: rest =>
      val (body, rest1) = 
        parse_bracketed[HP](parse_hp,"}",rest)
      val rest2 = parse_tok("*", rest1)
      rest2 match {
        case "@" :: "invariant" :: rest3 =>
          val rest4 = parse_tok("(", rest3)
          val (invs, rest5) = parse_list(",",parse_formula0)(rest4)
          val rest6 = parse_tok(")", rest5)
          (Loop(body,True,invs), rest6)
        case _ =>
          (Loop(body,True, Nil), rest2)
      }
    case _ => throw new ParseFailure("repeat", (), inp)
  }

  def parse_check: Tokens => (HP, Tokens) = inp => inp match {
      case "?"::rest =>
        val (fm, rest1) = parse_formula0(rest)
        (Check(fm), rest1)
      case _ => throw new ParseFailure("check", () , inp)
  }

  def parse_assign: Tokens => (HP, Tokens) = inp => inp match {
      case v :: ":=*" :: rest =>
        (AssignAny(v), rest)
      case v :: ":=" :: "*" :: rest =>
        (AssignAny(v), rest)
      case v :: ":="::rest =>
        val (tm, rest1) = parse_term(Nil)(rest)
        (Assign(v,tm), rest1)
      case _ => throw new ParseFailure("assign", (), inp)
  }

/*
 *  D ::= {a1' = t1, a2' = t2 ... }
 *
 *  p1 ; p2
 *  x := tm
 *  p1 ++ p2 
 *  ?fm
 *  p1* /\ h
 *  D /\ h
 */ 

  def or_comb[A](inp: Tokens,
                 ps: List[Tokens => (HP,Tokens)]): (HP,Tokens) = ps match {
    case p::ps1 => 
      try { p(inp) }
      catch { case e:ParseFailure => or_comb(inp,ps1) }
    case Nil => throw new ParseFailure("or_comb, no match", (), inp )        
  }

  def parse_atomic_hp: Tokens => (HP, Tokens) = inp =>  inp match {
    case "(":: rest =>
      parse_bracketed(parse_hp,")", rest)
    case _ =>
      or_comb(inp, List(parse_assign, parse_check,
                        parse_repeat, parse_evolve))
  }

  def parse_hp:  Tokens => (HP, Tokens) = inp => {
      parse_left_infix(";", ((p1:HP, p2:HP) => Seq(p1,p2)),
       parse_left_infix("++", ((p1:HP, p2:HP) => Choose(p1,p2)),
        parse_atomic_hp))(inp)
  }


  val hp_parser = (inp: String) => make_parser(parse_hp, inp)

  val parse_formula0 = 
    (inp: Tokens) => parse_formula((parse_infix_atom,parse_atom),Nil,inp)

  val formula_parser = (inp: String) => 
    make_parser(parse_formula0, inp);


  def parse_DLFormula: Tokens =>(DLFormula, Tokens) = inp => inp match{
    case "["::rest =>
      val (hp,rest1) = parse_bracketed(parse_hp, "]", rest)
      val (fm, rest2) = parse_DLFormula(rest1)
      (Box(hp, fm), rest2)
    case _ => 
      val (fm, rest) = parse_formula0(inp)
      (NoModality(fm), rest)
    
  }

  def parse_sequent: Tokens => (Sequent, Tokens) = inp => {

    val (lst, rest) = 
          if(inp.head == "|-") (Nil,inp)
          else parse_list(",",parse_formula0)(inp)
    val rest1 = parse_tok("|-", rest)
    val (dlfm, rest2) = parse_DLFormula(rest1)
    (Sequent(lst,dlfm), rest2)
  }


  val dlformula_parser = (inp: String) => 
    make_parser(parse_DLFormula, inp);

  val sequent_parser = (inp: String) =>
    make_parser(parse_sequent, inp)



  def strip_quant: FOFormula => (Tokens, FOFormula) = fm => fm match {
    case Forall(x,yp@Forall(y,p))=> 
      val (xs,q) = strip_quant(yp);
      (x::xs,q)
    case Exists(x,yp@Exists(y,p))=> 
      val (xs,q) = strip_quant(yp);
      (x::xs,q)
    case Forall(x,p) => (List(x),p)
    case Exists(x,p) => (List(x),p)
    case _ => (Nil, fm)
  }

  def list_delimit(d: String,lst: List[String]): String = lst match {
    case Nil => ""
    case s1:: Nil => s1
    case s1::rest => s1 + d + list_delimit(d,rest)
  }


  def bracket[A,B]: Boolean => Int => 
    (A => B => Unit) => A => B => Unit = 
      p => n => f => x => y => {
        if( p ) print("(") else ();
        f(x)(y);
        if( p ) print(")") else ();
      }

  def string_of_bracket[A,B]: Boolean => Int => 
    (A => B => String) => A => B => String = 
      p => n => f => x => y => {
        val sb = new StringBuilder()
        if( p ) sb.append("(") else ();
        sb.append(f(x)(y));
        if( p ) sb.append(")") else ();
        sb.toString()
      }



  def print_formula: (Int => Pred => Unit) => FOFormula => Unit = pfn => {
    def print_formula1: Int => FOFormula => Unit = pr => fm => fm match {
      case False => print("false")
      case True => print("true")
      case Atom(pargs) => pfn(pr)(pargs)
      case Not(p) => bracket (pr > 10)(1)(print_prefix(10))("~")(p)
      case And(p,q) => bracket (pr > 8)(0)(print_infix(8)("&"))(p)(q)
      case Or(p,q) => bracket (pr > 6)(0)(print_infix(6)("|"))(p)(q)
      case Imp(p,q) => bracket (pr > 4)(0)(print_infix(4)("==>"))(p)(q)
      case Iff(p,q) => bracket (pr > 2)(0)(print_infix(2)("<=>"))(p)(q)
      case Forall(x,p) => 
        bracket(pr>0)(2)(print_qnt)("forall")(strip_quant(fm))
      case Exists(x,p) => 
        bracket(pr>0)(2)(print_qnt)("exists")(strip_quant(fm))
    }
    def print_qnt: Token => ((Tokens,FOFormula)) => Unit = qname => b => {
      val (bvs, bod) = b;
      print(qname);
      bvs.foreach(v => print(" " + v));
      print(". ");
      print_formula1(0)(bod)
    }
    def print_prefix: Int => Token => FOFormula => Unit = newpr => sym => p => {
      print(sym); 
      print("(");
      print_formula1(newpr+1)(p);
      print(")");
    }
    def print_infix: Int => Token => FOFormula => FOFormula => Unit =
      newpr => sym => p => q => {
        print_formula1(newpr+1)(p);
        print(" "+sym+" ");
        print_formula1(newpr)(q)
      }
    print_formula1(0)
  }


  def string_of_formula: (Int => Pred => String) => FOFormula => String 
   = pfn => {
    def string_of_formula1: Int => FOFormula => String 
     = pr => fm => fm match {
      case False => "false"
      case True => "true"
      case Atom(pargs) => pfn(pr)(pargs)
      case Not(p) => 
        string_of_bracket(pr > 10)(1)(string_of_prefix(10))("~")(p)
      case And(p,q) => 
        string_of_bracket (pr > 8)(0)(string_of_infix(8)("&"))(p)(q)
      case Or(p,q) => 
        string_of_bracket (pr > 6)(0)(string_of_infix(6)("|"))(p)(q)
      case Imp(p,q) => 
        string_of_bracket (pr > 4)(0)(string_of_infix(4)("==>"))(p)(q)
      case Iff(p,q) => 
        string_of_bracket (pr > 2)(0)(string_of_infix(2)("<=>"))(p)(q)
      case Forall(x,p) => 
        string_of_bracket(pr>0)(2)(string_of_qnt)("forall")(strip_quant(fm))
      case Exists(x,p) => 
        string_of_bracket(pr>0)(2)(string_of_qnt)("exists")(strip_quant(fm))
    }
    def string_of_qnt: Token => ((Tokens,FOFormula)) => String = qname => b => {
      val (bvs, bod) = b;
      val sb = new StringBuilder()
      sb.append(qname);
      bvs.foreach(v => sb.append(" " + v));
      sb.append(". ");
      sb.append(string_of_formula1(0)(bod))
      sb.toString()
    }
    def string_of_prefix: Int => Token => FOFormula => String 
     = newpr => sym => p => {
      val sb = new StringBuilder()
      sb.append(sym); 
      sb.append("(");
      sb.append(string_of_formula1(newpr+1)(p))
      sb.append(")")
      sb.toString()
    }
    def string_of_infix: Int => Token => FOFormula => FOFormula => String =
      newpr => sym => p => q => {
        val sb = new StringBuilder()
        sb.append(string_of_formula1(newpr+1)(p))
        sb.append(" "+sym+" ")
        sb.append(string_of_formula1(newpr)(q))
        sb.toString()
      }
    string_of_formula1(0)
  }

  def print_qformula: (Int => Pred => Unit) 
                       => FOFormula => Unit = pfn => fm => {
//    print("<<");
    print_formula(pfn)(fm);
//    print(">>");
  }


  def string_of_qformula: (Int => Pred => String) 
                       => FOFormula => String = pfn => fm => {
//    print("<<");
    string_of_formula(pfn)(fm);
//    print(">>");
  }

  def print_term: Int => Term => Unit = prec => fm => fm match {
    case Var(x) => print(x)
    case Num(n) => print(n.toString)
    case Fn("^",List(tm1,tm2)) => 
      print_infix_term(true)(prec)(24)("^")(tm1)(tm2)
    case Fn("/",List(tm1,tm2)) => 
      print_infix_term(true)(prec)(22)(" /")(tm1)(tm2)
    case Fn("*",List(tm1,tm2)) => 
      print_infix_term(false)(prec)(20)(" *")(tm1)(tm2)
    case Fn("-",List(tm1,tm2)) => 
      print_infix_term(true)(prec)(18)(" -")(tm1)(tm2)
    case Fn("+",List(tm1,tm2)) => 
      print_infix_term(false)(prec)(16)(" +")(tm1)(tm2)
    case Fn("::",List(tm1,tm2)) => 
      print_infix_term(false)(prec)(14)(" +")(tm1)(tm2)
    case Fn(f,args) => print_fargs(f)(args)
  }
  def print_fargs: Token => List[Term] => Unit = f => args => {
    print(f);
    if(args == Nil) () else {
      print("(");
      print_term(0)(args.head);
      (args.tail).foreach(t => {print(","); print_term(0)(t)});
      print(")");
    }
  }
  def print_infix_term: Boolean => Int => Int => Token => Term => Term => Unit =
    isleft => oldprec => newprec => sym => p => q => {
      if(oldprec>newprec) print("(") else ();
      print_term(if(isleft) newprec else (newprec + 1))(p);
      print(sym);
      if(sym.charAt(0) == ' ') print(" ") else ();
      print_term(if(isleft) (newprec+1) else newprec)(q);
      if (oldprec > newprec) print(")") else ();
    }

  def string_of_term: Int => Term => String = prec => fm => fm match {
    case Var(x) => x
    case Num(n) => n.toString()
    case Fn("^",List(tm1,tm2)) => 
      string_of_infix_term(true)(prec)(24)("^")(tm1)(tm2)
    case Fn("/",List(tm1,tm2)) => 
      string_of_infix_term(true)(prec)(22)(" /")(tm1)(tm2)
    case Fn("*",List(tm1,tm2)) => 
      string_of_infix_term(false)(prec)(20)(" *")(tm1)(tm2)
    case Fn("-",List(tm1,tm2)) => 
      string_of_infix_term(true)(prec)(18)(" -")(tm1)(tm2)
    case Fn("+",List(tm1,tm2)) => 
      string_of_infix_term(false)(prec)(16)(" +")(tm1)(tm2)
    case Fn("::",List(tm1,tm2)) => 
      string_of_infix_term(false)(prec)(14)(" +")(tm1)(tm2)
    case Fn(f,args) => string_of_fargs(f)(args)
  }
  def string_of_fargs: Token => List[Term] => String = f => args => {
    val sb = new StringBuilder()
    sb.append(f);
    if(args == Nil) "" else {
      sb.append("(");
      sb.append(string_of_term(0)(args.head))
      (args.tail).foreach(t => {sb.append(","); 
                                sb.append(string_of_term(0)(t))})
      sb.append(")");
      sb.toString()
    }
  }
  def string_of_infix_term: Boolean => Int => Int => Token 
                            => Term => Term => String =
    isleft => oldprec => newprec => sym => p => q => {
      val sb = new StringBuilder()
      if(oldprec>newprec) sb.append("(") else ();
      sb.append(string_of_term(if(isleft) newprec else (newprec + 1))(p))
      sb.append(sym);
      if(sym.charAt(0) == ' ') sb.append(" ") else ();
      sb.append(string_of_term(if(isleft) (newprec+1) else newprec)(q))
      if (oldprec > newprec) sb.append(")") else ();
      sb.toString()
    }


  def printert(tm: Term): Unit = {
    print_term(0)(tm)
  }

  def string_of_Term(tm: Term): String = {
    string_of_term(0)(tm)
  }

  def print_atom:  Int => Pred => Unit = prec => fm => fm match {
    case R(p,args) => 
      if(comparators.contains(p) && (args.length == 2))
        print_infix_term(false)(12)(12)(" " + p)(args.apply(0))(args.apply(1))
      else print_fargs(p)(args)
    case _ => throw new Error("print_atom: nonatomic input")
  }

  def string_of_atom:  Int => Pred => String = prec => fm => fm match {
    case R(p,args) => 
      if(comparators.contains(p) && (args.length == 2))
       string_of_infix_term(false)(12)(12)(" " + p)(args(0))(args(1))
      else string_of_fargs(p)(args)
    case _ => throw new Error("print_atom: nonatomic input")
  }

  val print_FOFormula: FOFormula => Unit = print_qformula(print_atom);

  val string_of_FOFormula: FOFormula => String = 
      string_of_qformula(string_of_atom);

//----
  def string_of_HP(hp: HP): String = hp match {
    case Assign(s,t) => 
      s + " := " + string_of_Term(t)
    case AssignAny(s) =>
      s + " := *"
    case Check(fm) =>
      "?( " + string_of_FOFormula(fm) + ")"
    case Seq(p1,p2) =>
      string_of_HP(p1) + "; " + string_of_HP(p2)
    case Choose(p1,p2) =>
      string_of_HP(p1) + " ++ " + string_of_HP(p2)
    case Loop(p1,h, inv_hints) =>
      "{" + string_of_HP(p1) + "} * & " + string_of_FOFormula(h)
    case Evolve(d,h,inv_hints, sol_hints) =>
      val sb = new StringBuilder()
      sb.append("{")
      val tlst = d.map( (pr: (String, Term)) => 
                         pr._1 +"' = " + string_of_Term(pr._2) )
      sb.append(list_delimit(",", tlst))
      sb.append("; ")
      sb.append(string_of_FOFormula(h))
      sb.append("}")
      sb.toString()
  }


  def string_of_DLFormula(fm: DLFormula): String  = fm match {
    case NoModality(fm1) => string_of_FOFormula(fm1)
    case Box(hp, fm1) => 
      "[" + string_of_HP(hp) + "]" + string_of_DLFormula(fm1)
  }

  def string_of_Goal(g: Goal): String = g match {
    case Sequent(ctxt, phi) =>
      val flst = ctxt.reverse.map(fm => string_of_FOFormula(fm))
      val sb = new StringBuilder()
      sb.append(list_delimit(",",flst))
      sb.append("  |-  ")
      sb.append(string_of_DLFormula(phi))
      sb.toString()
//    case FOGoal(fm) => 
//      string_of_FOFormula(fm)
  }


//------- redlog output

  def redlog_of_formula(fm: FOFormula) :  String  = fm match {
      case False => "false"
      case True => "true"
      case Atom(R(r,List(lhs, rhs))) => 
        "(" + redlog_of_term(lhs) + ")" + r +
        "(" + redlog_of_term(rhs) + ")"
      case Atom(_) => throw new Error("non-binary relation")
      case Not(p) => 
        "not("+ (redlog_of_formula(p)) + ")"
      case And(p,q) => 
        "(" + redlog_of_formula(p) + ") and (" + redlog_of_formula(q) + ")" 
      case Or(p,q) => 
        "(" + redlog_of_formula(p) + ") or (" + redlog_of_formula(q) + ")" 
      case Imp(p,q) => 
        "(" + redlog_of_formula(p) + ") impl (" + redlog_of_formula(q) + ")" 
      case Iff(p,q) => 
        "(" + redlog_of_formula(p) + ") equiv (" + redlog_of_formula(q) + ")" 
      case Forall(x,p) => 
        "all(" + x + "," + redlog_of_formula(p) + ")" 
      case Exists(x,p) => 
        "ex(" + x + "," + redlog_of_formula(p) + ")" 
    }

  def redlog_of_term(tm: Term): String = tm match {
    case Var(x) => x
    case Num(n) => n.toString()
    case Fn("^",List(tm1,tm2)) => 
      "(" + redlog_of_term(tm1) + ") ** (" + redlog_of_term(tm2) + " )"
    case Fn("/",List(tm1,tm2)) => 
      "(" + redlog_of_term(tm1) + ") / (" + redlog_of_term(tm2) + " )"
    case Fn("*",List(tm1,tm2)) => 
      "(" + redlog_of_term(tm1) + ") * (" + redlog_of_term(tm2) + " )"
    case Fn("-",List(tm1,tm2)) => 
      "(" + redlog_of_term(tm1) + ") - (" + redlog_of_term(tm2) + " )"
    case Fn("-",List(tm)) => 
      "-(" + redlog_of_term(tm) + ") "
    case Fn("+",List(tm1,tm2)) => 
      "(" + redlog_of_term(tm1) + ") + (" + redlog_of_term(tm2) + " )"
    case _ => throw new Error ("don't know how to redlogify " + tm)
  }


//------- mathematica output
  import com.wolfram.jlink._

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
      case "<" => "Less"
      case "<=" => "LessEqual"
      case ">" => "Greater"
      case ">=" => "GreaterEqual"
    }


    def mathematica_of_formula(fm: FOFormula) :  Expr  = fm match {
      case False => math_sym("False")
      case True => math_sym("True")
      case Atom(R(r,List(lhs, rhs))) => 
        bin_fun(math_name(r), 
                mathematica_of_term(lhs),
                mathematica_of_term(rhs))
      case Atom(_) => throw new Error("non-binary relation")
      case Not(p) => 
        un_fun("Not", mathematica_of_formula(p))
      case And(p,q) => 
        bin_fun("And", mathematica_of_formula(p),mathematica_of_formula(q))
      case Or(p,q) => 
        bin_fun("Or", mathematica_of_formula(p),mathematica_of_formula(q))
      case Imp(p,q) => 
        bin_fun("Implies", mathematica_of_formula(p),
                           mathematica_of_formula(q))
      case Iff(p,q) => 
        bin_fun("Equivalent", mathematica_of_formula(p),
                              mathematica_of_formula(q))
      case Forall(x,p) => 
        val (bvs, p1) = strip_quant(fm)
        val math_bvs = bvs.map(math_sym)
        bin_fun("ForAll", new Expr(math_sym("List"), math_bvs.toArray),
                          mathematica_of_formula(p1))
      case Exists(x,p) => 
        val (bvs, p1) = strip_quant(fm)
        val math_bvs = bvs.map(math_sym)
        bin_fun("Exists", new Expr(math_sym("List"), math_bvs.toArray),
                          mathematica_of_formula(p1))
    }


}





class RedlogParser(in: InputStream) 
 extends StdTokenParsers with Application { 
  type Tokens = StdLexical ; val lexical = new StdLexical 
  lexical.delimiters ++= List(":", "$", "(", ")", "+", "-", "*", "/").iterator
 
   val br = new BufferedReader(new InputStreamReader(in))
   var ins = ""
   var ln = br.readLine()
   while (ln != null && ln != "START$"){
     println( ln)
     ln = br.readLine()
   }
   ln = br.readLine()
   while (ln != null && ln != "END$"){
     println( ln)
     ins = ins + ln
     ln = br.readLine()
   }


   println("input = " + ins)

// these are from a parsercombinator tutorial
  def expr: Parser[Int]
   = term*(keyword("+") ^^^ {(x: Int, y: Int) 
                           => x + y} 
                    | keyword("-") ^^^ {(x: Int, y: Int) 
                              => x - y}) 
  def term
   = factor*(this.keyword("*").^^^ {(x: Int, y: Int) 
                             => x * y}  
             | keyword("/") ^^^ {(x: Int, y: Int) 
                                =>  x / y}) 
  def factor: Parser[Int] = 
    "(" ~> expr <~  ")" | numericLit ^^ (_.toInt) 

//  def padding: Parser[Unit] =
//    success | keyword ("START") ~ "$"


 // this seems to work for now
  def boolLit: Parser[FOFormula] = 
    ident ^^ (x => x match { 
      case "true" => True 
      case  "false" => False})


  def redlogLine: Parser[FOFormula] = 
    numericLit ~> ":" ~> boolLit <~ "$"

// skip until you hit "START"
// read the next line
///  def redlogLine: Parser[(Int, ] = 
    

  Console.println(redlogLine(new lexical.Scanner(ins))) 



   def result : FOFormula = 
     redlogLine(new lexical.Scanner(ins)) match {
       case Success(r,_) => r
       case _ => throw new java.lang.Error("parse failure")
   }


} 

*/



