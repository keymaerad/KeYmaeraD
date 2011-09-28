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

    def doIt(w:Any):String = w match {
      case ee:(_,_) => {
        ee._1 match {
          case x:Fn => ee._2 match {
            case tm:Term => {
              assert(x.ps.size==0) //not sure if this is catched earlier / if Exception should be used
              doIt(termToXmlString(x)+"' == "+termToXmlString(tm))
            }
            case _ => throw new Exception("(Fn,Term) expected")
          }
          case _ => throw new Exception("(Fn,Term) expected")
        }
      }
      case f  :Formula  => doIt(formulatoXmlString(f))
    //case l  :List[_]  => l.map(el => doIt(el)).mkString(if(xmlTagName.length==0) " & " else "")
      case l  :List[_]  => l.map(el => doIt(el)).mkString(if(xmlTagName.length==0) " & " else "&amp;")
    //case str:String   => prefix+(if(xmlTagName.length>0) "<" +xmlTagName+">" else "")+str+(if(xmlTagName.length>0) "</"+xmlTagName+">" else "")+suffix
      case str:String   => str
      case None         => ""
      case Some(el:Any) => doIt(el)
      case _            => throw new Exception()
    }

    //doIt(v)
    prefix+(if(xmlTagName.length>0) "<" +xmlTagName+">" else "")+doIt(v)+(if(xmlTagName.length>0) "</"+xmlTagName+">" else "")+suffix
  }
//}}}
}

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

sealed abstract class Forb
case class EndsEq(f:Formula   ,l:List[Automaton#Location]) extends Forb
case class Choice(c:Connective,forbS:List[Forb]) extends Forb

class Automaton {
//{{{
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
//var init : Formula = True
  var forb : Forb = EndsEq(False,List())

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
        start = a1.start
        ends  = a2.ends
        a1.ends.foreach( end => end.add_transition(a2.start))
      case Choose(p1: HP, p2: HP) =>
        val a1 = new Automaton(p1)
        val a2 = new Automaton(p2)
        start = new Location
        locations = start :: a1.locations ::: a2.locations
        ends  = a1.ends ::: a2.ends
        start.add_transition(a1.start)
        start.add_transition(a2.start)
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
      case _ => throw new TooWeak("automaton simulate * assignments and quantified assignments / diff eqS")
    }
    this
  //}}}
  }

  def this(f: Formula) = {
  //{{{
      this

      def negate_connection(c:Connective):Connective = c match {
        case Or => And
        case And => Or
        case _ => throw new Exception("should have been cought by normalize")
      }

      val f_normalized = DNFize.normalize(f)

      f_normalized match {
        case Binop(c,f1,f2) => {
          val automatons = List(new Automaton(f1),new Automaton(f2))
          start = new Location
          locations = start :: automatons.map(a1 => a1.locations).reduce(_:::_)
          forb = Choice(negate_connection(c),automatons.map(a1 => a1.forb))
          automatons.foreach(a1 => start.add_transition(a1.start))
          ends = automatons.map(a1 => a1.ends).reduce(_:::_)
          this
        }
        case Atom(R(_,_)) | True | False => {
          locations = List(new Location,new Location)
          start = locations(0)
          ends  = List(locations(1))
          forb = EndsEq(True,ends)
          val t = start.add_transition(ends(0))
          t.check = Some(Not(f_normalized))
          this
        }
        case Modality(Box,hp,phi) => {
          val a1 = new Automaton(hp)
          val a2 = new Automaton(phi)
          a1.ends.foreach(end => end.add_transition(a2.start))
          ends = a2.ends
          forb = a2.forb
          this
        }
        case Modality(Diamond,_,_) => throw new TooWeak("Diamond modality")
        case _ => throw new Exception("should have been eleminited by normalize")
      }

      /*
      //{{{

      def get_atoms(h:Formula):List[Formula] = h match {
        case Binop(And,f1,f2) => List(f1,f2).map(get_atoms).reduce(_:::_)
        case True => List()
        case Binop(_,_,_) | Not(_) => throw new Exception
        case _ => List(h)
        //case Atom(R(_,_)) | Modality | False => List(h)
      }

      val clauses = DNFize(f)
      assert(clauses.length>0)
      if(clauses.length>1) choice_automaton(clauses.map(h => this(h)),Or)
      else
      {
        val atoms = get_atoms(clauses(0))
        assert(atoms.length>0)
        if(atoms.length>1) choice_automaton(atoms.map(h => this(h)),And)
        else
        {
          val h = atoms[0]
          h match {
            case Atom(R(_,_)) | False | True => {
              start = new Loation
              locations = List(start)
              ends      = List(start)
              TODO -- set forb
              //forb
            }
            case Modality(_,hp,phi) => {
              val a = this(hp)
              TODO -- append this(phi)
              //this(phi)
            }
          }

        }
      }
      var init = Deparse(g.ctxt)
      if(init!="") init+= " & "
      init+= "loc()==l"+a.getId(a.start)
      var forb = Deparse(DNFize.normalize(Not(phi)))
      assert(a.ends.length>0)
      forb+= " & ("+a.ends.map(end => "loc()==l"+a.getId(end)).mkString(" | ")+")"
      //endstate
      //init+= " & isendstate=="+(if(a.isEnd(a.start)) "1" else "0")
      //forb+= " & isendstate==1"
      //}}}
      */
  //}}}
  }

  def add_location():Automaton#Location = {val newL=new Location;locations=locations:+newL;newL}

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
//}}}
}

object Spaceex {
//{{{
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
    res+="iter-max = -1\n"
    res+="rel-err = 1.0e-12\n"
    res+="abs-err = 1.0e-15\n"
    res+="output-format = TXT"
    res
    //sampling-time = 0.5
    //}}}
  }

  def forb_to_string(forb: Forb,a: Automaton):String = forb match {
  //{{{
    case EndsEq(f,locations) => "("+Deparse(f)+") & "+locations.map(l => "loc()==l"+a.getId(l)).mkString(" | ")
    case Choice(c,forbS) => forbS.map(forbS => "("+forb_to_string(forbS,a)+")").mkString(if(c==Or) " | " else " & ")
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
        toSpaceexAutomaton(a)

        println(a.toStr('txt))
        Util.str2file("DLBanyan/_.dot",a.toStr('graph))

        Util.str2file("DLBanyan/_.cfg",configFile("",forb_to_string(a.forb,a)))
        Util.str2file("DLBanyan/_.xml",toSX(a).toString())

        val spaceex_path=System.getenv("SPACEEX")
        if(spaceex_path!=null && spaceex_path.length>0) throw new Exception("set SPACEEX env var")
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
