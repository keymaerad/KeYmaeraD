package DLBanyan

class TooWeak       (e:String) extends Exception("no way found to support "+e)
class NotImplemented(e:String) extends Exception(e)
class TODO          (e:String) extends Exception(e)

object Deparse {
//{{{
//deparse ~= parse^-1 -- not sure which of de- and un- would be the right prefix tho q-:
  var varS : List[String] = Nil
  //assumptions:
  //-char . is only used for Fn(_,Nil) by docOfTerm
  //-char . is only used for forall/exists by docOfFormula (or by calling docOfTerm)
  //-always a space between . and forall/exists
  //-Printing fcts make returns char . only by calling docOfTerm or docOfFormula
  private def retrieve_varS(s:String):Unit = {varS = varS ::: "[a-zA-Z]+(?=\\.)".r.findAllIn(s).toList }

  def apply(v:Any, xmlTagName:String="", prefix:String="", suffix:String=""):String = {

    def spaceexizeSyntax(s:String):String = {
    //{{{
      //TODO: not thought through solution according to "0 -" -> "-" -- probably some case where it won't do like "x - 0 - y"
      def escapeXml(s:String):String = if(xmlTagName=="") s else s.replaceAll("<","&lt;").replaceAll(">","&gt;")
      escapeXml(s.replaceAll("0 -","-").replaceAll("([^<>!=])=","$1==").replaceAll("\\.",""))
     }
   //}}}
    def termToXmlString(tm: Term):String = {
    //{{{
      val sw = new java.io.StringWriter()
      val d = Printing.docOfTerm(tm)
      d.format(70, sw)
      val res = sw.toString
      //println("Printing.docOfTerm")
      //println(res)
      //println(tm)
      retrieve_varS(res)
      //escapeXml(res).replaceAll("\\.","")
      spaceexizeSyntax(res)
    }
    //}}}
    def formulatoXmlString(f: Formula):List[String] =
    //{{{
    {
      //var quantified_varS: List[String] = Nil
      f match {
        case Atom(R(_,_)) | True | False => {
          val res = Printing.stringOfFormula(f)
          retrieve_varS(res)
          //List(escapeXml(res.replaceAll("([^<>!=])=","$1==")).replaceAll("\\.",""))
          List(spaceexizeSyntax(res))
        }
        //case Quantifier(Forall,Real,v,g) => assert(quantified_varS.indexOf(v)== -1);quantified_varS=quantified_varS:+v;formulatoXmlString(g)
        case Quantifier(_,Real,_,_) => throw new NotImplemented("quantifiers not supported")
        case Quantifier(Forall,_   ,_,_) => throw new TooWeak("distributed quantifier")
        case Binop(And, f1, f2) => formulatoXmlString(f1) ::: formulatoXmlString(f2)
        case Binop(Or , f1, f2) => List("("+formulatoXmlString(f1).mkString(" & ") +")|("+ formulatoXmlString(f2).mkString(" & ")+")")
        case Binop(_,_,_) => throw new TODO("Not supported yet "+f)
        case Not(_) => throw new TODO("Not not supported yet -- "+f)
        case Quantifier(Exists,_,_,_) | Modality(_,_,_) => throw new TooWeak("Exists quantifier and modality")
        //case _ => throw new Exception("i should have covered every case")
      }
    }
    //}}}

    v match {
      case ee:(_,_) => {
        ee._1 match {
          case x:Fn => ee._2 match {
            case tm:Term => {
              assert(x.ps.size==0) //not sure if this is catched earlier / if Exception should be used
              apply(termToXmlString(x)+"' == "+termToXmlString(tm),xmlTagName,prefix,suffix)
            }
            case _ => throw new Exception("(Fn,Term) expected")
          }
          case _ => throw new Exception("(Fn,Term) expected")
        }
      }
      case f  :Formula  => apply(formulatoXmlString(f),xmlTagName,prefix,suffix)
      case l  :List[_]  => l.map(el => apply(el,xmlTagName,prefix,suffix)).mkString(if(xmlTagName.length==0) " & " else "")
      case str:String   => prefix+(if(xmlTagName.length>0) "<" +xmlTagName+">" else "")+str+(if(xmlTagName.length>0) "</"+xmlTagName+">" else "")+suffix
      case None         => ""
      case Some(el:Any) => apply(el,xmlTagName,prefix,suffix)
      case _            => throw new Exception()
    }
  }
//}}}
}

class Automaton(hp: HP) {
  class Location {
    //{{{
    // None value for {inv, evolve, assign} ~= identity funtion
    var evolve : Option[List[(Fn,Term)]] = None
    var inv    : Option[Formula]         = None
    var transitions :   List[Transition] = Nil

    class Transition(val to: Automaton#Location) {
      var check:  Option[Formula]          = None
      var assign: Option[List[(Fn, Term)]] = None
    }

    def add_transition(to: Automaton#Location): Transition = {
      val t = new Transition(to)
      transitions = t :: transitions
      t
    }
    //}}}
  }
  var locations : List[Automaton#Location] = Nil
  var start : Automaton#Location = new Location //will always be overriden
  var ends : List[Automaton#Location] = Nil //only used for translation

  hp match {
    //{{{
    case Check(h: Formula) => 
      locations = List(new Location,new Location)
      locations(0).add_transition(locations(1)).check = Some(h)
      start = locations(0)
      ends  = List(locations(1))
      this
    case Assign(vs) => //vs: List[(Fn,Term)]
      locations = List(new Location,new Location)
      locations(0).add_transition(locations(1)).assign = Some(vs)
      start = locations(0)
      ends  = List(locations(1))
      this
    case Evolve(derivs, h,_,_) => //derivs: List[(Fn,Term)], h: Formula
      locations = List(new Location)
      locations(0).inv = Some(h)
      locations(0).evolve = Some(derivs)
      start = locations(0)
      ends  = List(locations(0))
      this
    case Seq(p1: HP, p2: HP) => 
      val a1 = new Automaton(p1)
      val a2 = new Automaton(p2)
      locations = a1.locations ::: a2.locations
      start = a1.start
      ends  = a2.ends
      a1.ends.foreach( end => end.add_transition(a2.start))
      this
    case Choose(p1: HP, p2: HP) =>
      val a1 = new Automaton(p1)
      val a2 = new Automaton(p2)
      locations = new Location :: a1.locations ::: a2.locations
      ends  = a1.ends ::: a2.ends
      start = locations(0)
      start.add_transition(a1.start)
      start.add_transition(a2.start)
      this
    case Loop(p1: HP,_,_) =>
      /*
      var a1 = new Automaton(p1)
      a1.ends.foreach(end => end.add_transition(a1.start))
      a1
      */
      val a1      = new Automaton(p1)
      locations   = a1.locations
      ends        = a1.ends
      start       = a1.start
      ends.foreach(end => end.add_transition(a1.start))
      this
    case _ => throw new TooWeak("automaton simulate * assignments and quantified assignments / diff eqS")
    //}}}
  }

  def getId  (l:Automaton#Location) = {val res = locations.indexOf(l);assert(res!= -1);res}
  def isEnd  (l:Automaton#Location) = ends.indexOf(l)!= -1
  def isStart(l:Automaton#Location) = l==start

  def size = locations.size

  def toStr(format:Symbol) = {
  //{{{
    //'graph => graphviz format
    assert(format=='txt || format=='graph)

    var res = ""
    if(format=='graph) res+= "digraph hybrid_automata {\nE[label=\"\" shape=none]\n"

    locations.foreach(loc => {
      val id = getId(loc)

      res += (if(format=='txt) "===Loc"+id else id+" [label=\""+id)

      if(loc.evolve != None) res+= (if(format=='graph) " -- " else "\n") + "evolve: " + Deparse(loc.evolve)
      if(loc.inv    != None) res+= (if(format=='graph) " -- " else "\n") + "inv: "    + Deparse(loc.inv   )

      if(format=='graph)
      {
        if(isEnd(loc)) res+= "\" shape=\"doublecircle"
        res+= "\"]"
        if(isStart(loc)) res+= "\nE->"+id
      }

      loc.transitions.foreach(t => {
        res+= "\n"+id+"->"+getId(t.to)
        if(format=='graph) res+= " [label=\""
        if(t.check  != None) res+= (if(format=='txt) " | " else "")+"check: " +Deparse(t.check )
        if(format=='graph && t.check!=None && t.assign!=None) res+= " -- "
        if(t.assign != None) res+= (if(format=='txt) " | " else "")+"assign: "+Deparse(t.assign)
        if(format=='graph) res+= "\"]"
      })
      res+="\n"
    })

    if(format=='graph) res+="}"
    res
  //}}}
  }
}

object Spaceex {
//{{{
  private object DNFize {
  //{{{
  //conjunction of equations <=> no Not,Quantifier,Modality + dnf
    private def negateAtom(a:Atom):Atom = a match
    //{{{
    {
      case Atom(R(rel,tmS)) => rel match {
        case ">"  => Atom(R("<=",tmS))
        case "<"  => Atom(R(">=",tmS))
        case ">=" => Atom(R("<" ,tmS))
        case "<=" => Atom(R(">" ,tmS))
        case "==" => Atom(R("!=",tmS))
        case "!=" => Atom(R("==",tmS))
        case _ => throw new TODO("lookup all relations / their syntax -- context: "+a)
      }
    }
    //}}}
    //eleminates Not,Imp,Iff and catches Quantifier,Modality
    def simplify(f:Formula):Formula = f match {
    //{{{
      case Atom(_) | True | False => f
      case Binop(Iff,f1,f2) => simplify(Binop(Or,Binop(And,f1,f2),Binop(And,Not(f1),Not(f2))))
      case Binop(Imp,f1,f2) => simplify(Binop(Or,Not(f1),f2))
      case Binop(c,f1,f2) => Binop(c,simplify(f1),simplify(f2))
      case Not(Binop(Or ,f1,f2)) =>   simplify(Binop(And,Not(f1),Not(f2)))
      case Not(Binop(And,f1,f2)) =>   simplify(Binop(Or ,Not(f1),Not(f2)))
      case Not(Binop(c,f1,f2))   =>   simplify(Not(simplify(Binop(c,f1,f2))))
      case Not(Atom(p)) => negateAtom(Atom(p))
      case Not(True) => False
      case Not(False) => True
      case Not(Not(g)) => g
      case Not(g) => {simplify(g);throw new Exception("this should never have been called -- instead another Exception should have been thrown befor")}
      case Quantifier(_,Real,_,_) => throw new NotImplemented("quantifiers not supported")
      case Quantifier(_,_,_,_) => throw new TooWeak("distributed quantifier")
      case Modality(_,_,_) => throw new NotImplemented("multiple modalities not supported")
    }
    //}}}
    def apply(f:Formula):List[Formula] = {
      val g = simplify(f)
      g match {
        case Binop(Or ,f1,f2) => apply(f1) ::: apply(f2)
        case Binop(And,f1,f2) => {
          var res:List[Formula] = List()
            apply(f1).foreach(fleft => {
              apply(f2).foreach(fright => res = Binop(And,fleft,fright)::res)
            })
          res
        }
        case Atom(_) | True | False => List(g)
        case Binop(Iff,_,_) | Binop(Imp,_,_) | Not(_) | Quantifier(_,_,_,_) | Modality(_,_,_) => throw new Exception("these classes should have been eliminted by simplify before")
      }
    }
  }
  //}}}

  private def toSpaceexAutomaton(a:Automaton):Unit =
  //{{{
  {
    for(l <- a.locations)
    {
      if(l.inv != None)
      {
        val inv_dnf = DNFize(l.inv.get)
        assert(inv_dnf.length==1)
        l.inv = Some(inv_dnf(0))
      }
      for(t <- l.transitions)
      {
        if(t.check != None)
        {
          val check_dnf = DNFize(t.check.get)
          assert(check_dnf.length>0)
          t.check = Some(check_dnf(0))
          for(i <- 1 to check_dnf.length-1)
          {
            var new_t=l.add_transition(t.to)
            new_t.check=Some(check_dnf(i))
            new_t.assign=t.assign
          }
        }
      }
    }
  }
  //}}}

  private def toSX(a:Automaton) = {
  //{{{
    //
    assert(Deparse.varS.length>0,"assumption that toSX would be called max one time apparently false")

    //only purpose of following paragraph is to set varS
    for(l <- a.locations)
    {
      Deparse(l.inv)
      Deparse(l.evolve)
      for(t <- l.transitions)
      {
        Deparse(t.check)
        Deparse(t.assign)
      }
    }

    def make_evolve_explicit(v: Any):List[(Fn,Term)] = v match
    {
      case l:List[(Fn,Term)] => {
        var varS_todo:Set[String] = Deparse.varS.toSet
        l.foreach(tuple => varS_todo=varS_todo-(tuple._1.f))
        var res = l
        varS_todo.foreach(v => res=((Fn(v,Nil),Num(Exact.zero)))::res )
        res
      }
      case None => make_evolve_explicit(Nil)
      case Some(v: Any) => make_evolve_explicit(v)
      case _ => throw new Exception("unexpected input type")
    }

    //actual deparsing
    var locations_str = ""
    var transitions_str = ""
    for(l <- a.locations)
    {
      val id = a.getId(l).toString()
      locations_str+= "  <location id=\""+id+"\" name=\"l"+id+"\">\n"
      locations_str+= Deparse(l.inv,"invariant","    ","\n")
    //locations_str+= Deparse(l.evolve,"flow","    ","\n")
      locations_str+= Deparse(make_evolve_explicit(l.evolve),"flow","    ","\n")
      locations_str+= "  </location>\n"
      for(t <- l.transitions)
      {
        transitions_str+= "  <transition source=\""+id+"\" target=\""+a.getId(t.to).toString()+"\">\n"
        transitions_str+= Deparse(t.check ,                                                                    "guard"     ,"    ","\n")
        transitions_str+= Deparse(t.assign,                                                                    "assignment","    ","\n")
      ////no assertion that var isendstate is already used
      //transitions_str+= Deparse(List((Fn("isendstate",Nil),Num((if(a.isEnd(t.to))Exact.one else Exact.zero)))),"assignment","    ","\n")
        transitions_str+= "  </transition>\n"
      }
    }

    var res = ""
    def xmlParam(v:String,t:String) = "  <param name=\""+v+"\" type=\""+t+"\" d1=\"1\" d2=\"1\" local=\"true\" dynamics=\"any\"/>\n"
    Deparse.varS.toSet.foreach((v: String) => res+=xmlParam(v,"real"))

    res+=locations_str
    res+=transitions_str

    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">\n"+"<component id=\"system\">\n"+res+"</component>\n</sspaceex>"
  //}}}
  }

  def apply(filename: String):Unit = {

    object Util
    {
      def str2file(file:String,text:String){
        //{{{
          def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
              val p = new java.io.PrintWriter(f)
                try { op(p) } finally { p.close() }
          }
          import java.io._
          val data = Array(text)
          printToFile(new File(file))(p => {
              data.foreach(p.println)
          })
        //}}}
      }

      def runCmd(cmd:String) = {
      //{{{
        import sys.process._ //requires 2.9
        val stdout = cmd !!;
        stdout
      //}}}
      }
    }

    def configFile(init:String,forbidden:String):String = {
      //{{{
      var res=""
      res+="initially = \""+init+"\"\n"
      res+="forbidden = \""+forbidden+"\"\n"
      res+="scenario = \"phaver\"\n"
      res+="directions = \"uni32\"\n"
      res+="time-horizon = 4\n"
      res+="iter-max = 1\n"
      res+="rel-err = 1.0e-12\n"
      res+="abs-err = 1.0e-15\n"
      res+="output-format = TXT"
      res
      //sampling-time = 0.5
      //}}}
    }

    val fi = 
      new java.io.FileInputStream(filename)

    val dlp = new DLParser(fi)

    dlp.result match {
      case Some(g:Sequent) => {
        //val print_fm = (fm:Formula) => println(Printing.stringOfFormula(fm))
        //g.ctxt .foreach(print_fm)
        //g.scdts.foreach(print_fm)
        if(g.scdts.size !=1) throw new NotImplemented("Sequent with one goal expected")
        var h = g.scdts(0)
        h match {
          case Modality(Box,hp,phi) => {
            val a = new Automaton(hp)
            toSpaceexAutomaton(a)
            println(a.toStr('txt))
            Util.str2file("DLBanyan/_.dot",a.toStr('graph))

            var init = Deparse(g.ctxt)
            if(init!="") init+= " & "
            init+= "loc()==l"+a.getId(a.start)
            var forb = Deparse(DNFize.simplify(phi))
            assert(a.ends.length>0)
            forb+= " & ("+a.ends.map(end => "loc()==l"+a.getId(end)).mkString(" | ")+")"
            //endstate
            //init+= " & isendstate=="+(if(a.isEnd(a.start)) "1" else "0")
            //forb+= " & isendstate==1"
            Util.str2file("DLBanyan/_.cfg",configFile(init,forb))
            Util.str2file("DLBanyan/_.xml",toSX(a).toString())

            val spaceex_path=System.getenv("SPACEEX")
            assert(spaceex_path!=null && spaceex_path.length>0,"set SPACEEX env var")
            println(Util.runCmd(spaceex_path+" -m DLBanyan/_.xml --config DLBanyan/_.cfg"))
          }
          case _ => throw new TooWeak("Diamond modality")
        }
      }
      case None => throw new Exception("DLParser.result didn't returned a sequent")
    }
  }
//}}}
}

object Test {

  def main(args: Array[String]) {

    /* uncomment -> java.lang.NoClassDefFoundError: org/apache/commons/cli/Options
    import org.apache.commons.cli.Options
    import org.apache.commons.cli.CommandLine

    new org.apache.commons.cli.Options();
    def parse() : CommandLine = {
      var opts = new org.apache.commons.cli.Options();
      opts.addOption("input", true, "input dl file");
      var parser = new org.apache.commons.cli.GnuParser();
      parser.parse( opts, args);
    }
    val cmd = parse()

    Spaceex(cmd.getOptionValue("input"))
    */
    Spaceex(args(0))
  }
}
