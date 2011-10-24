package DLBanyan

class TooWeak       (e:String) extends Exception("no way found to support "+e)
class NotImplemented(e:String) extends Exception(e)
class TODO          (e:String) extends Exception(e)

object DNFize {
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
      case  "=" => Atom(R("!=",tmS))
      case "!=" => Atom(R("==",tmS))
      case _ => throw new TODO("lookup all relations / their syntax -- context: "+a)
    }
  }
  //}}}
  //eleminates Not,Imp,Iff and catches Quantifier,Modality(Diamond,_,_)
  def normalize(f:Formula):Formula = f match {
  //{{{
    case Atom(_) | True | False | Modality(Box,_,_) => f
    case Binop(Iff,f1,f2) => normalize(Binop(Or,Binop(And,f1,f2),Binop(And,Not(f1),Not(f2))))
    case Binop(Imp,f1,f2) => normalize(Binop(Or,Not(f1),f2))
    case Binop(c,f1,f2) => Binop(c,normalize(f1),normalize(f2))
    case Not(Binop(Or ,f1,f2)) =>   normalize(Binop(And,Not(f1),Not(f2)))
    case Not(Binop(And,f1,f2)) =>   normalize(Binop(Or ,Not(f1),Not(f2)))
    case Not(Binop(c,f1,f2))   =>   normalize(Not(normalize(Binop(c,f1,f2))))
    case Not(Atom(p)) => negateAtom(Atom(p))
    case Not(True) => False
    case Not(False) => True
    case Not(Not(g)) => g
    case Not(g) => {normalize(g);throw new Exception("this should never have been called -- instead another Exception should have been thrown befor")}
    case Quantifier(Forall,Real,_,_) => throw new TODO("forall quantifiers not supported")
    case Quantifier(Exists,Real,_,_) => throw new TooWeak("existencial quantifier")
    case Quantifier(_,_,_,_) => throw new TooWeak("distributed quantifier")
    case Modality(Diamond,_,_) => throw new TooWeak("Diamond Modality")
  }
  //}}}
  def apply(f:Formula):List[Formula] = {
    val g = normalize(f)
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
      case Modality(Box,_,_) => throw new Exception("should have been could before")
      case Binop(Iff,_,_) | Binop(Imp,_,_) | Not(_) | Quantifier(_,_,_,_) | Modality(Diamond,_,_) => throw new Exception("these classes should have been eliminted by normalize before")
    }
  }
//}}}
}

class Automaton {
//{{{
  sealed abstract class Forb
  case class EndsEq(f:Formula   ,l:List[Automaton#Location]) extends Forb
  case class Choice(c:Connective,forbS:List[Automaton#Forb]) extends Forb

  class Location {
    //{{{
    var autom = Automaton.this

    // None value for {inv, evolve, assign} ~= identity funtion
    var evolve : Option[List[(Fn,Term)]] = None
    var inv    : Option[Formula]         = None
    var transitions :   List[Transition] = Nil

    class Transition(val to: Automaton#Location) {
      val from = Location.this
      var check:  Option[Formula]          = None
      var assign: Option[List[(Fn, Term)]] = None
    }

    def add_transition(to: Automaton#Location): Transition = {
      val t = new Transition(to)
      transitions = t :: transitions
      t
    }

    def id      = {val res = autom.locations.indexOf(this);assert(res!= -1);res}
    def isEnd   = autom.ends.indexOf(this)!= -1
    def isStart = autom.start==this
    //}}}
  }
  var locations : List[Automaton#Location] = Nil
  var start : Automaton#Location = new Location //will always be overriden
  var ends : List[Automaton#Location] = Nil //only used for translation
  private var forb : Automaton#Forb = EndsEq(False,List())

  def this(hp: HP) = {
  //{{{
    this
    hp match {
      case Check(h: Formula) => 
        locations = List(new Location,new Location)
        locations(0).add_transition(locations(1)).check = Some(h)
        start = locations(0)
        ends  = List(locations(1))
      case Assign(vs) => //vs: List[(Fn,Term)]
        locations = List(new Location,new Location)
        locations(0).add_transition(locations(1)).assign = Some(vs)
        start = locations(0)
        ends  = List(locations(1))
      case Evolve(derivs, h,_,_) => //derivs: List[(Fn,Term)], h: Formula
        locations = List(new Location)
        locations(0).inv = Some(h)
        locations(0).evolve = Some(derivs)
        start = locations(0)
        ends  = List(locations(0))
      case Seq(p1: HP, p2: HP) => 
        val a1 = new Automaton(p1)
        val a2 = new Automaton(p2)
        locations = a1.locations ::: a2.locations
        locations.foreach(l => l.autom = this)
        start = a1.start
        ends  = a2.ends
        a1.ends.foreach( end => end.add_transition(a2.start))
      case Choose(p1: HP, p2: HP) =>
        val a1 = new Automaton(p1)
        val a2 = new Automaton(p2)
        start = new Location
        locations = start :: a1.locations ::: a2.locations
        locations.foreach(l => l.autom = this)
        ends  = a1.ends ::: a2.ends
        start.add_transition(a1.start)
        start.add_transition(a2.start)
      case Loop(p1: HP,_,_) =>
        val a1      = new Automaton(p1)
        locations   = a1.locations
        locations.foreach(l => l.autom = this)
        ends        = a1.ends
        start       = a1.start
        ends.foreach(end => end.add_transition(a1.start))
      case _ => throw new TooWeak("automaton simulate * assignments and quantified assignments / diff eqS")
    }
    this
  //}}}
  }

  def this(f: Formula) = {
  //{{{
      this

      val f_normalized = DNFize.normalize(f)

      f_normalized match {
        case Binop(c,f1,f2) => {
          val automatons = List(new Automaton(f1),new Automaton(f2))
          start = new Location
          locations = start :: automatons.map(a1 => a1.locations).reduce(_:::_)
          locations.foreach(l => l.autom = this)
          forb = Choice(c,automatons.map(a1 => a1.forb))
          automatons.foreach(a1 => start.add_transition(a1.start))
          ends = automatons.map(a1 => a1.ends).reduce(_:::_)
        }
        case Atom(R(_,_)) | True | False => {
          locations = List(new Location,new Location)
          locations.foreach(l => l.autom = this)
          start = locations(0)
          ends  = List(locations(1))
          forb = EndsEq(True,ends)
          val t = start.add_transition(ends(0))
          t.check = Some(Not(f_normalized))
        }
        case Modality(Box,hp,phi) => {
          val a1 = new Automaton(hp)
          val a2 = new Automaton(phi)
          locations = a1.locations ::: a2.locations
          locations.foreach(l => l.autom = this)
          start = a1.start
          a1.ends.foreach(end => end.add_transition(a2.start))
          ends = a2.ends
          forb = a2.forb
        }
        case Modality(Diamond,_,_) => throw new TooWeak("Diamond modality")
        case _ => throw new Exception("should have been eleminited by normalize")
      }
      this
  //}}}
  }

  def add_location():Automaton#Location = {val newL=new Location;locations=locations:+newL;newL}

  def size = locations.size

  def toStr(Stringifier : Any => String): String = {
  //{{{
    var res = ""
    locations.foreach(loc => {
      res += Stringifier(loc)
      loc.transitions.foreach(t => res+= Stringifier(t))
      res += "\n"
    })
    res
  //}}}
  }

  def forb_to_formula():Formula = {
  //{{{

    //val locVarName = stringifier('location_variable)
    val locVarName = "loc()"
    def locName(locId:Int) = "l"+locId

    //def locEq(locId: Int,rel: String): Formula = Atom(R(rel,List(Fn(locVarName,Nil),Num(new Exact.Rational(locId)))))
    def locEq(locId: Int,rel: String): Formula = Atom(R(rel,List(Fn(locVarName,Nil),Fn(locName(locId),Nil))))

    def connect(f1:Formula,locS1:List[Int],f2:Formula,locS2:List[Int],c:Connective):Formula = {
      assert(locS1.intersect(locS2).size==0)
      c match {
        case And => Binop(Or ,f1,f2)
        case Or  => {
          def clause(f:Formula,locS:List[Int]) = Binop(Or,f,locS.map(locId => locEq(locId,"!=")).reduce((f1,f2) => Binop(And,f1,f2)))
        //def clause(f:Formula,locS:List[Int],c:Connective) = Binop(Or,f,locS.map(locId => locEq(locId,if(c==And) "!=" else "==")).reduce((f1,f2) => Binop(c,f1,f2)))
           Binop(And,locS1.union(locS2).map(locId => locEq(locId,"==")).reduce((f1,f2) => Binop(Or,f1,f2)),Binop(And,clause(f1,locS1),clause(f2,locS2))) 
        }
        case _   => throw new Exception("normalize should have been called before")
      }
    }

    def toFormula(forbi: Automaton#Forb): (Formula,List[Int]) = forbi match {
      case EndsEq(f,locations) => ((f :: locations.map(l => locEq(l.id,"=="))).reduce((f1,f2) => Binop(And,f1,f2)),locations.map(l => l.id))
      case Choice(c,forbS) => forbS.map(toFormula).reduce((l,r) => (connect(l._1,l._2,r._1,r._2,c),l._2 ::: r._2))
    }

    toFormula(forb)._1
  //}}}
  }
//}}}
}

object Spaceex {
//{{{
  //TODO
  //-rewrite this termToStr -- make string converstion manually -- rewrite retrieve_varS
  //-seperate to string code and spaceex specific code
  object Deparse {
  //{{{
    var varS : List[String] = Nil
    //assumptions:
    //-char . is only used for Fn(_,Nil) by docOfTerm
    //-char . is only used for forall/exists by docOfFormula (or by calling docOfTerm)
    //-always a space between . and forall/exists
    //-Printing fcts make returns char . only by calling docOfTerm or docOfFormula
    private def retrieve_varS(s:String):Unit = {varS = varS ::: "[a-zA-Z]+(?=\\.)".r.findAllIn(s).toList }

    def apply(v:Any, xmlTagName:String="", prefix:String="", suffix:String=""):String = {

      def formulaToStr(f:Formula):String = {
      //{{{
        def connectiveToStr(c:Connective):String = c match
        {
          case Or  => "|"
          case And => "&"
          case Imp => "=>"
          case Iff => "<=>"
        }
        f match {
          case Binop(c,f1,f2) => "("+formulaToStr(f1)+") "+connectiveToStr(c)+" ("+formulaToStr(f2)+")"
          case True    => "true"
          case False   => "false"
          case Not(f1) => "! ("+formulaToStr(f1)+")"
          case Atom(R(rStr,terms)) => {
            assert(terms.length==2,"until now only relations with arity 2 used")
            termToStr(terms(0))+" "+(if(rStr=="=") "==" else rStr)+" "+termToStr(terms(1))
          }
          case Quantifier(_,_,_,_) | Modality(_,_,_) => throw new Exception("shoudn't be needed -- should have been eleminted/handled before calling this")
        }
      //}}}
      }

      def termToStr(tm:Term):String = {
      //{{{
        def spaceexizeSyntax(s:String):String = {
        //{{{
          //TODO: not thought through solution according to "0 -" -> "-" -- probably some case where it won't do like "x - 0 - y"
          def escapeXml(s:String):String = if(xmlTagName=="") s else s.replaceAll("<","&lt;").replaceAll(">","&gt;")
          escapeXml(s.replaceAll("0 -","-").replaceAll("([^<>!=])=","$1==").replaceAll("\\.",""))
         }
       //}}}

        val sw = new java.io.StringWriter()
        val d = Printing.docOfTerm(tm)
        d.format(70, sw)
        val res = sw.toString
        retrieve_varS(res)
        spaceexizeSyntax(res)
      //}}}
      }

      def formulaToStrFlat(f: Formula): List[String] = f match {
      //{{{
          case Binop(And,f1,f2) => formulaToStrFlat(f1) ::: formulaToStrFlat(f2)
          case _ => List(formulaToStr(f))
      //}}}
      }

      def doIt(w:Any):String = w match {
        case ee:(_,_) => {
          ee._1 match {
            case x:Fn => ee._2 match {
              case tm:Term => {
                assert(x.ps.size==0) //not sure if this is catched earlier / if Exception should be used
                doIt(termToStr(x)+"' == "+termToStr(tm))
              }
              case _ => throw new Exception("(Fn,Term) expected")
            }
            case _ => throw new Exception("(Fn,Term) expected")
          }
        }
        //case f  :Formula  => doIt(formulaToStrFlat(f))
        case f  :Formula  => doIt(formulaToStr(f))
        case l  :List[_]  => l.map(el => doIt(el)).mkString(" & ")
        case str:String   => str
        case None         => ""
        case Some(el:Any) => doIt(el)
        case _            => throw new Exception
      }

      var res = doIt(v)
      if(xmlTagName!="")
      {
        res = res.replaceAll("&","&amp;").replaceAll("<","&lt;").replaceAll(">","&gt;")
        res =  "<" +xmlTagName+">" + res
        res += "</"+xmlTagName+">"
      }
      prefix+res+suffix
    }
  //}}}
  }

  object Stringify {

    //Deparse required
    def toSX(a:Automaton) = {
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
        val id = l.id.toString()
        locations_str+= "  <location id=\""+id+"\" name=\"l"+id+"\">\n"
        locations_str+= Deparse(l.inv,"invariant","    ","\n")
      //locations_str+= Deparse(l.evolve,"flow","    ","\n")
        locations_str+= Deparse(make_evolve_explicit(l.evolve),"flow","    ","\n")
        locations_str+= "  </location>\n"
        for(t <- l.transitions)
        {
          transitions_str+= "  <transition source=\""+id+"\" target=\""+t.to.id.toString()+"\">\n"
          transitions_str+= Deparse(t.check ,                                                                    "guard"     ,"    ","\n")
          transitions_str+= Deparse(t.assign,                                                                    "assignment","    ","\n")
        ////no assertion that var isendstate is already used
        //transitions_str+= Deparse(List((Fn("isendstate",Nil),Num((if(t.to.isEnd)Exact.one else Exact.zero)))),"assignment","    ","\n")
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

    //Deparse required
    def graphStr(a: Automaton):String = {
    //{{{
      //graphviz format
      def stringifier_graph(v: Any):String = {
        //{{{
        var res = ""
        v match {
          case l:Automaton#Location => {
            res += l.id+" [label=\""+l.id

            if(l.evolve != None) res+= " -- evolve: " + Deparse(l.evolve)
            if(l.inv    != None) res+= " -- inv: "    + Deparse(l.inv   )

            if(l.isEnd) res+= "\" shape=\"doublecircle"
            res+= "\"]"
            if(l.isStart) res+= "\nE->"+l.id
          }
          case t:Automaton#Location#Transition => {
            res+= "\n"+t.from.id+"->"+t.to.id
            res+= " [label=\""
            if(t.check  != None) res+= "check: " +Deparse(t.check )
            if(t.check!=None && t.assign!=None) res+= " -- "
            if(t.assign != None) res+= "assign: "+Deparse(t.assign)
            res+= "\"]"
          }
        }
        res
        //}}}
      }
      "digraph hybrid_automata {\nE[label=\"\" shape=none]\n"+a.toStr(stringifier_graph)+"}"
    //}}}
    }
    def txtStr(a: Automaton):String = {
    //{{{
      def stringifier_txt(v: Any):String = {
        //{{{
        var res = ""
        v match {
          case l:Automaton#Location => {
            res +=  "===Loc"+l.id
            if(l.evolve != None) res+= "\nevolve: " + Deparse(l.evolve)
            if(l.inv    != None) res+= "\ninv: "    + Deparse(l.inv   )
          }
          case t:Automaton#Location#Transition => {
            res+= "\n"+t.from.id+"->"+t.to.id
            if(t.check  != None) res+= " | check: " +Deparse(t.check )
            if(t.assign != None) res+= " | assign: "+Deparse(t.assign)
          }
        }
        res
        //}}}
      }
      a.toStr(stringifier_txt);
    //}}}
    }
  }

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

  private def toSpaceexAutomaton(a:Automaton):Unit =
  //{{{
  {
    for(l <- a.locations)
    {
      if(l.inv != None)
      {
        val inv_dnf = DNFize(l.inv.get)
        assert(inv_dnf.length>0)
        if(inv_dnf.length==1)
          l.inv = Some(inv_dnf(0))
        else
        {
          for(i <- 0 to inv_dnf.length-1)
          {
            val newL = a.add_location()
            newL.inv = Some(inv_dnf(i))
            newL.evolve = l.evolve
            l.add_transition(newL)
            newL.add_transition(l)
          }
          l.inv = None
          l.evolve = None
        }
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


  def configFile(init:String,forbidden:String):String = {
    //{{{
    var res=""
    res+="initially = \""+init+"\"\n"
    res+="forbidden = \""+forbidden+"\"\n"
    res+="scenario = \"phaver\"\n"
    res+="directions = \"uni32\"\n"
    res+="time-horizon = 4\n"
    res+="iter-max = -1\n"
    res+="rel-err = 1.0e-12\n"
    res+="abs-err = 1.0e-15\n"
    res+="output-format = TXT"
    res
    //sampling-time = 0.5
    //}}}
  }

  def apply(filename: String):Unit = {

    val fi = 
      new java.io.FileInputStream(filename)

    val dlp = new DLParser(fi)

    dlp.result match {
      case Some(g:Sequent) => {

        //val print_fm = (fm:Formula) => println(Printing.stringOfFormula(fm))
        //g.ctxt .foreach(print_fm)
        //g.scdts.foreach(print_fm)

        val h : Formula = (g.ctxt.map(f => Not(f)) ::: g.scdts).reduce((f1,f2) => Binop(Or,f1,f2))
        val a = new Automaton(h)
        println(Stringify.txtStr(a))

        toSpaceexAutomaton(a)

        Util.str2file("DLBanyan/_.dot",Stringify.graphStr(a))
        Util.str2file("DLBanyan/_.cfg",configFile("loc()==l"+a.start.id,Deparse(a.forb_to_formula)))
        Util.str2file("DLBanyan/_.xml",Stringify.toSX(a))

        val spaceex_path=System.getenv("SPACEEX")
        if(spaceex_path==null || spaceex_path.length==0) throw new Exception("set SPACEEX env var")
        println(Util.runCmd(spaceex_path+" -m DLBanyan/_.xml --config DLBanyan/_.cfg"))
      }
      case None => throw new Exception("DLParser.result didn't returned a sequent")
    }
  }
//}}}
}

object Test {

  def main(args: Array[String]) {

    /* uncomment -> java.lang.NoClassDefFoundError: org/apache/commons/cli/Options
    //{{{
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
    //}}}
    */
    if(args.length==0) throw new Exception("argument required: dl file required");
    Spaceex(args(0))
  }
}
