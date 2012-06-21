
package KeYmaeraD
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
import scala.util.parsing.input.CharArrayReader.EofCh
import scala.collection.mutable.HashSet


/* class KEYLexical extends StdLexical {
 override def identChar = letter | elem('_') | elem('#') | elem('$') | elem('\'')

}   */

class KEYLexical() extends StdLexical() {

  case class FloatingPointLit(chars: String) extends Token {
    override def toString = chars
  }

  override def token: Parser[Token] =
    ( identChar ~ rep( identChar | digit )              ^^ { case first ~ rest => processIdent(first :: rest mkString "") }
    | delim
    | '(' ~ delim ~ ')'                                 ^^ { case '(' ~ d ~ ')' => Identifier(d.chars) }
    | '(' ~ '0' ~ '-' ~ ')'                             ^^ { _ => Identifier("0-") }
    | '\"' ~ rep( chrExcept('\"', '\n', EofCh) ) ~ '\"' ^^ { case '\"' ~ chars ~ '\"' => StringLit(chars mkString "") }
    | '\"' ~> failure("unclosed string literal")
    | floatLit                                          ^^ { case f => FloatingPointLit(f) }
    | signedIntegerLit                                  ^^ { case i => NumericLit(i) }
    )

  // legal identifier chars other than digits
  override def identChar = letter | elem('_') | elem('\'') | elem('#') | elem('$')

  def nonZeroDigit = elem('1') | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
  def integerLit =
      ( elem('0')                 ^^ { _.toString() }
      | rep1(nonZeroDigit, digit) ^^ { _ mkString "" }
      )

  def signedIntegerLit =
      ( elem('-') ~ integerLit ^^ { case a ~ b => a+b }
      | integerLit )
  def plusMinusIntegerLit =
      ( elem('+') ~ integerLit ^^ { case a ~ b => a+b }
      | signedIntegerLit )

  def floatLit =
    ( signedIntegerLit ~ '.' ~ integerLit ~ (elem('e') |  elem('E')) ~ plusMinusIntegerLit ^^ { case a ~ b ~ c ~ d ~ e => a+b+c+d+e }
    | signedIntegerLit                    ~ (elem('e') |  elem('E')) ~ plusMinusIntegerLit ^^ { case a ~ b ~ c => a+b+c }
    | signedIntegerLit ~ '.' ~ integerLit                                                  ^^ { case a ~ b ~ c => a+b+c }
    )


  /** The set of reserved identifiers: these will be returned as `Keyword's */
  override val reserved = new HashSet[String] ++ List( /* "\\",
                              "sorts", "functions", "problem", "forall", "exists",  */
                              "true", "false", "invariant",
                              "solution", "strengthen", "if", "then", "fi",
                              "generic", "extends", "oneof", "object",
                             "schemaVariables", "modalOperator", "operator",
                             "program", "formula", "term", "variables", "skolemTerm",
                             "location", "function", "modifies", "varcond", "typeof",
                             "elemTypeof", "new", "newLabel", "not", "same","compatible",
                             "sub", "strict", "staticMethodReference", "notFreeIn", "freeLabelIn",
                             "static", "enumConstant", "notSameLiteral", "isReferenceArray",
                             "isArray", "isReference", "isNonImplicit", "isEnumType", "dependingOn",
                             "dependingOnMod", "isQuery", "isNonImplicitQuery", "hasSort", "isLocalVariable",
                             "notIsLocalVariable", "isFirstOrderFormula", "isUpdated", "sameHeapDepPred",
                             "bind", "forall", "exists", "subst", "ifEx", "for", "if", "then", "else",
                             "sum", "bsum", "product", "include", "includeLDTs", "classpath", "bootclasspath",
                             "noDefaultClasses", "javaSource", "noJavaModel", "withOptions", "optionDecl",
                             "settings", "true", "false", "sameUpdateLevel", "inSequentState", "closegoal",
                             "heuristicsDecl", "noninteractive", "displayname", "oldname", "helptext",
                             "replacewith", "addrules", "addprogvars", "heuristics", "find", "add", "assume",
                             "predicates", "functions", "nonRigid", "inter", "rules", "problem", "chooseContract",
                             "proof", "contracts", "invariants",
                             // The first two guys are not really meta operators, treated separately
                             "inType", "isInReachableState", "isAbstractOrInterface", "containerType",
                             "forall", "exists", "true", "false",
                             "solution", "invariant", "strengthen", "sorts",
                             "if", "then", "else", "fi", "while", "do", "end",
                             "repeat", "until", "skip", "abort"
    )

  /** The set of delimiters (ordering does not matter) */
  override val delimiters = new HashSet[String] ++ List(
                             "\\sorts", "\\functions",
                             "\\problem", "\\forall", "\\exists",
                             "{", "}", "\\[", "\\]",  "\\<", "\\>", "&",
                               ",", ";", ":", "(", ")", "[", "]",
                              "=", "<", ">", ">=", "<=",
                             "!", "!=", "+", "-", "*", "/", "^",
                             "++", ":=", "@", "?",
                             //"&",
                             "|", "<->", "->", "==>", "."
                             /* "~",
                             ";", "/", ":", "::", ":=", ".", "..",
                             ",", "(", ")", "[", "]", "{", "}", "[]",
                             "@", "||", "|", "&", "!", "->", "=", "!=",
                             "==>", "^^", "~", "%", "*", "+", "^",
                             ">", ">=", "<", "<=", "\t", "\r", "\n",
                             "''",   "<->" */
    )

}




class KEYParser(ins : String)
 extends StdTokenParsers {
  type Tokens = StdLexical ;
  val lexical = new KEYLexical
  /* lexical.delimiters ++= List("\\sorts", "\\functions",
                             "\\problem", "\\forall", "\\exists", "{", "}", "\\[", "\\]",  "\\<", "\\>", "&",
                               ",", ";", ":", "(", ")", "[", "]",
                              "=", "<", ">", ">=", "<=",
                             "!", "!=", "+", "-", "*", "/", "^",
                             "++", ":=", "@", "?",
                             //"&",
                             "|", "<->", "->", "==>", "."
                             /* "~",
                             ";", "/", ":", "::", ":=", ".", "..",
                             ",", "(", ")", "[", "]", "{", "}", "[]",
                             "@", "||", "|", "&", "!", "->", "=", "!=",
                             "==>", "^^", "~", "%", "*", "+", "^",
                             ">", ">=", "<", "<=", "\t", "\r", "\n",
                             "''",   "<->" */
                             ).iterator   // !!!WE MAY NEED MORE HERE!!!

   lexical.reserved ++= List( /* "\\", "\\sorts", "\\functions", "\\problem", "\\forall", "\\exists", */
                              "true", "false", "invariant",
                              "solution", "strengthen", "if", "then", "fi",
                              "generic", "extends", "oneof", "object",
                             "schemaVariables", "modalOperator", "operator",
                             "program", "formula", "term", "variables", "skolemTerm",
                             "location", "function", "modifies", "varcond", "typeof",
                             "elemTypeof", "new", "newLabel", "not", "same","compatible",
                             "sub", "strict", "staticMethodReference", "notFreeIn", "freeLabelIn",
                             "static", "enumConstant", "notSameLiteral", "isReferenceArray",
                             "isArray", "isReference", "isNonImplicit", "isEnumType", "dependingOn",
                             "dependingOnMod", "isQuery", "isNonImplicitQuery", "hasSort", "isLocalVariable",
                             "notIsLocalVariable", "isFirstOrderFormula", "isUpdated", "sameHeapDepPred",
                             "bind", "forall", "exists", "subst", "ifEx", "for", "if", "then", "else",
                             "sum", "bsum", "product", "include", "includeLDTs", "classpath", "bootclasspath",
                             "noDefaultClasses", "javaSource", "noJavaModel", "withOptions", "optionDecl",
                             "settings", "true", "false", "sameUpdateLevel", "inSequentState", "closegoal",
                             "heuristicsDecl", "noninteractive", "displayname", "oldname", "helptext",
                             "replacewith", "addrules", "addprogvars", "heuristics", "find", "add", "assume",
                             "predicates", "functions", "nonRigid", "inter", "rules", "problem", "chooseContract",
                             "proof", "contracts", "invariants",
                             // The first two guys are not really meta operators, treated separately
                             "inType", "isInReachableState", "isAbstractOrInterface", "containerType",
                             "forall", "exists", "true", "false",
                             "solution", "invariant", "strengthen",
                             "if", "then", "else", "fi", "while", "end", "do",
                             "repeat", "until"
                             ).iterator   //!!! WE MAY NEED TO CHANGE OR DELETE SOMETHING HERE!!!    */



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
     prod*("+" ^^^ {(x:Term, y:Term) =>  Fn("+", List(x,y))}  |
          "-" ^^^ {(x: Term, y: Term) => Fn("-", List(x,y))})


   def prod: Parser[Term] =
     factor*("*" ^^^ {(x: Term, y: Term) => Fn("*", List(x,y))} |
            "/" ^^^ {(x: Term, y: Term) => Fn("/", List(x,y))}) |
            "-" ~> prod ^^ { x => Fn("-", List(x))}




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
     term ~ ("=" | "!=" | "<" | ">" | "<=" | ">=" ) ~ term ^^
       { case t1 ~ r ~ t2 =>
          R(r, List(t1,t2))}



   def formula00 : Parser[Formula] =
     "\\forall" ~> ident ~ ident ~ ";" ~ formula00 ^^
               { case "R" ~ x ~ ";" ~ f  => Quantifier(Forall, x, Real, f)
                 case c ~ x ~ ";"  ~ f  => Quantifier(Forall, x, St(c), f) } |
     "\\exists" ~> ident ~ ident ~ ";" ~ formula00 ^^
               { case "R" ~ x ~ ";" ~ f  => Quantifier(Exists, x, Real, f)
                 case c ~ x ~ ";" ~  f => Quantifier(Exists, x, St(c), f)} |
     //"\forall" ~> ident ~ ":" ~ ident ~ ";" ~ formula00 ^^
     //          { case x ~ ":" ~ c ~ ";" ~ f => Quantifier(Forall,St(c), x, f)} |
     //"\exists" ~> ident ~ ":" ~ ident ~ ";" ~ formula00 ^^
     //          { case x ~ ":" ~ c ~ ";" ~ f => Quantifier(Exists,St(c),x, f)} |  //I DO NOT KNOW IF WE NEED THESE TWO!!!
       formula0


   def formula0 : Parser[Formula] =
     formula1*( "<->" ^^^ {(f1:Formula,f2:Formula) => Binop(Iff,f1,f2)})


   // Implication is right-associative.
   def formula1 : Parser[Formula] =
      rep1sep(formula2, "->") ^^
        ((lst) => lst.reduceRight((f1:Formula,f2:Formula) => Binop(Imp,f1,f2)))

   def formula2 : Parser[Formula] =
     formula3*( "|" ^^^ {(f1:Formula,f2:Formula) => Binop(Or,f1,f2)})

   def formula3 : Parser[Formula] =
     formula4*( "&" ^^^ {(f1:Formula,f2:Formula) => Binop(And,f1,f2)})

   def formula4 : Parser[Formula] =
     "!" ~> formula5 ^^ {fm => Not(fm)} |
     formula5

   def formula5 : Parser[Formula] =
   "\\forall" ~> ident ~ ident ~ ";" ~ formula00 ^^
               { case "R" ~ x ~ ";" ~ f  => Quantifier(Forall, x, Real, f)
                 case c ~ x ~ ";"  ~ f  => Quantifier(Forall, x, St(c), f) } |
     "\\exists" ~> ident ~ ident ~ ";" ~ formula00 ^^
               { case "R" ~ x ~ ";" ~ f  => Quantifier(Exists, x, Real, f)
                 case c ~ x ~ ";" ~  f => Quantifier(Exists, x, St(c), f)} |
     "(" ~> formula00 <~  ")" |
     pred ^^ (x => Atom(x))  |
     "true" ^^^ True |
     "false" ^^^ False |
     // XXX doesn't work right for e.g. "[hp] forall x . ..."
     ("\\[" ~> hp <~ "\\]") ~ formula4 ^^ {case a ~ f => Modality(Box,a,f)} |
     ("\\<" ~> hp <~ "\\>") ~ formula4 ^^ {case a ~ f => Modality(Diamond,a,f)}


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
       case Quantifier(q, v, c, f) =>
         Quantifier(q, v, c, freeVarsAreFns(v :: bndVars, f))
       case Modality(m,hp,phi) =>
         Modality(m,freeVarsAreFns_HP(bndVars, hp), freeVarsAreFns(bndVars, phi))
     }


   def formula : Parser[Formula] =
     formula00 ^^ {fm => freeVarsAreFns(Nil, fm) }



   def hp : Parser[HP] =
     hp1*(";" ^^^ {(p1,p2) => Seq(p1,p2)})  |
     hp1

   def hp1 : Parser[HP] =
     hp2*("++" ^^^ {(p1,p2) => Choose(p1,p2)}) |
     hp2


   def hp2 : Parser[HP] =
      ( hp3 <~ "*") ~ annotation("invariant") ^^
            { case x ~ invs => Loop(x, True, invs)}    |
      hp3


  /* def hp3 : Parser[HP] =
   *   "(" ~> hp <~  ")" |
   *   "?" ~> formula00 ^^ { x => Check(x)}  |
   *   ident <~ ":=" <~ "*" ^^ { x  => AssignAny(Fn(x,Nil))} |
   *   function <~ ":=" <~ "*" ^^ { f  => AssignAny(f)} |
   *   (ident <~ ":=") ~ term ^^ {case x ~ t => Assign(List((Fn(x,Nil),t)))} |
   *   (function <~ ":=") ~ term ^^ {case f ~ t => Assign(List((f,t)))} |
   *   // (("forall" ~> ident <~  ":") ~
   *   // ident ~ function <~ ":=") ~ term ^^
   *   //  {case i ~ c ~ f ~ v => AssignQuantified(i,St(c),List((f,v)))} |
   *   // (("forall" ~> ident <~  ":") ~
   *   // ident ~ function <~ ":=") ~ "*" ^^
   *   //  {case i ~ c ~ f ~ "*" => AssignAnyQuantified(i,St(c),f)} |
   *   // { alpha }*
   *   // ( "(" ~> hp <~ ")" <~ "*") ~ annotation("invariant") ^^
   *    //     { case x ~ invs => Loop(x, True, invs)} |
   *   // {x' = theta, ..., h}
   *   ("{" ~> rep1sep(diffeq, ",") <~ ",")  ~
   *       (formula00 <~ "}") ~ annotation("invariant") ~ annotation("strengthen") ^^ //~ annotation("strengthen") ^^
   *         {case dvs ~ f ~ invs ~ sols => Evolve(dvs,f,invs,sols)}  |   //MAY NEED TO CHECK CAREFULLY//
   *    //("{" ~> rep1sep(diffeq, ","))  ~
   *    //   (formula00 <~ "}") ~ annotation("invariant") ~ annotation("strengthen") ^^ //~ annotation("strengthen") ^^
   *    //     {case dvs ~ f ~ invs ~ sols => Evolve(dvs,f,invs,sols)}
   *      ("{" ~> rep1sep(diffeq, ",") <~ "}") ~ annotation("invariant") ~ annotation("strengthen") ^^ //~ annotation("strengthen") ^^
   *        {case dvs ~ invs ~ sols => Evolve(dvs,True,invs,sols)}
   *   // forall i : C  f(v)' = theta & h
   *   // XXX  TODO figure out how to read apostrophes in a sane way
   *  //   ("forall" ~> ident <~ ":") ~ ident ~
   * //    ("{" ~> rep1sep(qdiffeq, ",") <~ ";") ~ (formula00 <~ "}") ~ annotation("solution") ^^
   * //    { case i ~ c ~ vs  ~ h ~ sols =>
   * //      EvolveQuantified(i,St(c),vs,h, sols) }  //WE MAY DO NOT NEED THIS IN KEY
   * //TO DO : IF THEN ELSE WHILE REPEAT BLAH BLAH BLAH
   */


   def hp3 : Parser[HP] =
      "(" ~> hp <~  ")" |
      "?" ~> formula00 ^^ { x => Check(x)}  |
      ident <~ ":=" <~ "*" ^^ { x  => AssignAny(Fn(x,Nil))} |
      function <~ ":=" <~ "*" ^^ { f  => AssignAny(f)} |
      (ident <~ ":=") ~ term ^^ {case x ~ t => Assign(List((Fn(x,Nil),t)))} |
      (function <~ ":=") ~ term ^^ {case f ~ t => Assign(List((f,t)))} |
      ("{" ~> rep1sep(diffeq, ",") <~ ",")  ~
          (formula00 <~ "}") ~ annotation("weaken") ~ annotation("strengthen") ~ annotation("solution") ^^ //~ annotation("strengthen") ^^
            {case dvs ~ f ~ weaken ~ invs ~ sols => Evolve(dvs,f,invs,sols)}  |   //MAY NEED TO CHECK CAREFULLY//
      ("{" ~> rep1sep(diffeq, ",") <~ "}") ~ annotation("weaken") ~ annotation("strengthen") ~ annotation("solution") ^^ //~ annotation("strengthen") ^^
           {case dvs ~ weaken ~ invs ~ sols => Evolve(dvs,True,invs,sols)}  |
      ("if" ~> formula00 <~ "then") ~ (hp) <~ "fi" ^^
      {case fm ~ hp => Choose(Seq(Check(fm),hp), Check(Not(fm))) }  |
      ("if" ~> formula00 <~ "then") ~ (hp) ~ ("else" ~> hp) <~ "fi" ^^
      {case fm ~ thp ~ ehp => Choose(Seq(Check(fm),thp), Seq(Check(Not(fm)), ehp))}  |
      ("while" ~> formula00) ~ (hp) <~ "end" ^^
      {case fm ~ hp =>  Seq(Loop(Seq(Check(fm),hp), True, Nil),Check(Not(fm)))} |
      //("repeat" ~> hp <~ "until") ~ (formula00) <~ "end" ^^
      ("repeat" ~> hp <~ "until") ~ (formula00) ^^
      {case hp ~ fm =>  Seq(Loop(Seq(Check(Not(fm)),hp), True, Nil),Check(fm))} |
      "skip" ^^^ Check(True) |
      "abort" ^^^ Check(False)


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
    ident ^^ {case "R" => Real
              case s => St(s)}

  def sorts : Parser[List[Sort]] =
    "\\sorts" ~ "{" ~> repsep(sort, ";") <~ "}"  |
    "\\sorts" ~ "{" ~> repsep(sort, ";") <~ ";" <~ "}" |
    success(Nil)


  def functionsort : Parser[(String,(List[Sort],Sort))] =
    (sort ~ ident <~ "(") ~ (rep1sep(sort,",")) <~ "," <~ ")" ^^
      {case rtn ~ f ~ args => (f,(args,rtn))}  |
    (sort ~ ident <~ "(") ~ (rep1sep(sort,",")) <~ ")" ^^
      {case rtn ~ f ~ args => (f,(args,rtn))}  |
      (sort ~ ident) ^^
      {case c ~ f => (f, (Nil, c))}


 /*  def variablesort: Parser[(Sort, List[String])] =
    (sort ~ repsep(ident, ",")) ^^
      {case s ~ vargs => (s, vargs)}    */

    def variablesort: Parser[List[(String,(List[Sort],Sort))]] =
    (sort ~ rep1sep(ident, ",")) ^^
      {case s ~ vargs => {
      var vsrtsl : List[(String,(List[Sort],Sort))] = Nil
      for (v <- vargs) {
     vsrtsl =  (v, (Nil, s)) :: vsrtsl
      }
      vsrtsl
      }
      }



    def functionsorts: Parser[Map[String,(List[Sort],Sort)]] =
    "\\functions" ~> "{" ~> repsep(functionsort, ";") <~ ";" <~ "}" ^^
        {case fnsrts => scala.collection.immutable.HashMap.empty ++ fnsrts} |
    "\\functions" ~> "{" ~> repsep(functionsort, ";") <~ "}" ^^
        {case fnsrts => scala.collection.immutable.HashMap.empty ++ fnsrts} |
        success(scala.collection.immutable.HashMap.empty)

    /*def variablesorts: Parser[Map[String,(List[Sort],Sort)]] =
        "\\problem" ~> "{" ~> "\\[" ~> repsep(variablesort, ";") <~ "\\]" ^^
           {case varsrts  => {
           var varmap : Map[String,(List[Sort],Sort)] =  scala.collection.immutable.HashMap.empty
           for (vsrtl <- varsrts) {
           varmap = varmap ++ vsrtl
            }
            varmap
            }
              } |
            success(scala.collection.immutable.HashMap.empty) */

       def variablesorts: Parser[Map[String,(List[Sort],Sort)]] =
       repsep(variablesort, ";") ^^
       {case varsrts  => {
           var varmap : Map[String,(List[Sort],Sort)] =  scala.collection.immutable.HashMap.empty
           for (vsrtl <- varsrts) {
           varmap = varmap ++ vsrtl
            }
            varmap
            }
              } |
            success(scala.collection.immutable.HashMap.empty)

    /* def funvarsorts: Parser[Map[String,(List[Sort],Sort)]] =
        variablesorts   */


  /* def functionsort : Parser[(String,(List[Sort],Sort))] =
   * (ident <~ ":" <~ "(") ~ (repsep(sort,",") <~ ")" <~ "->") ~ sort ^^
   *   {case f ~ args ~ rtn => (f,(args,rtn))}
   */

  /* def functionsorts : Parser[Map[String,(List[Sort],Sort)]] =
   * "{" ~> repsep(functionsort, ",") <~ "}" ^^
   *    {case fnsrts => scala.collection.immutable.HashMap.empty ++ fnsrts }
   */

   def sequent : Parser[Sequent] =
    sorts ~> functionsorts ~ repsep(formula, ",") ~ ("==>" ~> repsep(formula,",")) ^^
        {case fnsrts ~ c ~ s => Sequent(fnsrts, c,s)}  |
    sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> formula <~ "}") ^^
       {case fnsrts ~ s => Sequent(fnsrts, Nil, List(s))}   |
    sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ "\\]") ~ (formula <~ "}") ^^
        {case fnsrts ~ varsrts ~ s => Sequent(fnsrts ++ varsrts, Nil, List(s))}  |
    sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ ";" <~ "\\]") ~ (formula <~ "}") ^^
        {case fnsrts ~ varsrts ~ s => Sequent(fnsrts ++ varsrts, Nil, List(s))}  |
   // sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ ";") ~ (repsep(hp | formula00, ";") <~ "\\]") ~ (formula00 <~ "}") ^^
    sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ ";") ~ (hp <~ "\\]") ~ (formula <~ "}") ^^
       {case fnsrts ~ varsrts ~ a ~ s => Sequent(fnsrts ++ varsrts, Nil, List(Modality(Box,a,s)))} |
   //     {case fnsrts ~ varsrts ~ hp ~ s => Sequent(fnsrts ++ varsrts, Nil, List(s))} |
   // sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ ";") ~ (repsep(hp | formula00, ";") <~ ";" <~ "\\]") ~ (formula00 <~ "}") ^^
   //     {case fnsrts ~ varsrts ~ hp ~ s => Sequent(fnsrts ++ varsrts, Nil, List(s))}
    sorts ~> functionsorts ~ ("\\problem" ~> "{" ~> "\\[" ~> variablesorts <~ ";") ~ (hp <~ ";" <~ "\\]") ~ (formula <~ "}") ^^
       {case fnsrts ~ varsrts ~ a ~ s => Sequent(fnsrts ++ varsrts, Nil, List(Modality(Box, a, s)))}

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




object KP {
  def openFile(f:String) : InputStream = {
    new FileInputStream(f)
  }


  def parseFormula(f:String) : Formula = {
    val keyp = new KEYParser(f)
    keyp.fm_result match {
      case Some(fm) => fm
      case None =>
        println("could not read a formula from " + f)
        False
    }
  }

}


