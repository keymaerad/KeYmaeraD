//TODO
//-toSpaceexAutomaton
//-compute init and forb
//-set start loop for composition
//-set param equal at init
//-alter deparse for assign
//TOTHINK
//-flat composition instead of hiearchical composition

package DLBanyan

class TooWeak       (e:String) extends Exception("no way found to support "+e)
class NotImplemented(e:String) extends Exception(e)
class TODO          (e:String) extends Exception(e)
casss AssertFail               extends Exception

def INAME(idStr:String) = "i_"+idStr
def LNAME(idStr:String) = "l" +idStr

object Util_Formula {
//{{{
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

  //conjunction of equations <=> no Not,Quantifier,Modality + dnf
  def DNFize(f:Formula):List[Formula] = {
  //{{{
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
  //}}}
  }

  isLinearCombination(f:Formula) = {
  //{{{
    f match {
      case Modality(_,_,_) => false
      case Binop (c,f1,f2) => isLinearCombination(f1) & isLinearCombination(f2)
      case Quantifier(_,_,_,_) => throw new TODO("get rid of quantifiers")
      case _ => true
    }
  //}}}
  }
//}}}
}

class Location(var transitions : List[Transition]        = Nil,
               val evolve      : Option[List[(Fn,Term)]] = None,
               val inv         : Option[Formula]         = None
              )

class Transition(val to     : Location
                 val check  : Option[Formula]          = None,
                 val assign : Option[List[(Fn, Term)]] = None
                )

class Automaton_Base(var locations : List[Location],
                     val start     : Location,
                     val ends      : List[Location],
                     val forb      : Formula = True
                    )

sealed abstract class Automaton_Composite
  case class Automaton_Base()                                                      extends Automaton_Composite
  case class Fork(c:Connective,left:Automaton_Composite,right:Automaton_Composite) extends Automaton_Composite

def toAutomaton(f: Formula):Automaton_Composite = {
//{{{
  def hpToAutomaton(hp: HP):Automaton_Base = {
    hp match {
      case Check(h: Formula) => 
        val end   = new Location
        val start = new Location(new Transition(end,Some(h)))
        Automaton_Base(List(start,end),start,List(end))
      /* TODO tbs */
      case _ => throw new TooWeak("automaton simulate * assignments and quantified assignments / diff eqS")
    }
  }

  if(Util_Formula.isLinearCombination(f)) return hpToAutomaton(Check(f))

  val f_normalized = Util_Formula.normalize(f)

  f_normalized match {
    case Binop(c,f1,f2) => Fork(c,toAutomaton(f1),toAutomaton(f2))
    case Modality(Box,hp,phi) => {
      val phiAutomaton = toAutomaton(phi)
      phiAutomaton match {
        case Automaton_Base => hpToAutomaton(Seq(hp,//TODO tbs
        case _ => throw new TODO("subclass of formulas are simulate-able")
      }
    }
    case Modality(Diamond,_,_) => throw new TooWeak("Diamond modality")
    case _ => throw new Exception("this should have been catched by isLinearCombination()")
  }
//}}}
}

def isStart(a:Automaton_Base,loc:Location) = a.ends.indexOf(loc)!= -1
def isEnd  (a:Automaton_Base,loc:Location) = a.start == loc

def retrieve_base_automata(ac:Automaton_Composite):List(Automaton_Base) = ac match {
//{{{
  case Automaton_Base => List(ac)
  case Fork(c,l,r)    => retrieve_base_automata(l) ::: retrieve_base_automata(r)
//}}}
}

def retrieve_varS(ac:Automaton_Composite):Set[String] = ac match {
//{{{
  case Fork(_,_,_) => Set()
  case a:Automaton_Base => {
    def retrieve(v:Any):List[String] = v match {
    //{{{
      case None => List()
      case Some(v_:Any) => retrieve(v_)
      case Term => v match {
        case Fn(symbolStr:String,l:List[Term]) => {
          if(l.size==0)
            List(symbolStr)
          else
            l.map(retrieve).reduce(_:::_)
        }
        case Var => throw new AssertFail //never saw Var occur before
        case Num => List()
      }
      case f:Formula => f match {
        case Atom(R(_,terms)) => {
          assert(terms.length==2,"until now only relations with arity 2 used")
          terms.map(retrieve).reduce(_:::_)
          terms(0) match {
            case Fn(varName:String,l:List[_]) => {assert(l.size==0);List(varName)}
            case _ => throw new AssertFail
          }
        }
        case Binop(_,f1,f2) => retrieve(f1) ::: retrieve(f2)
        case Not(f1) => retrieve(f1)
        case True | False => List()
        case Quantifier | Modality => throw new AssertFail
      }
      case _ => throw new AssertFail
    //}}}
    }
    val res = List()
    a.locations.foreach(l => {
      res = res ::: retrieve(l.evolve)
      res = res ::: retrieve(l.inv)
      l.transitions(t => {
        res = res ::: retrieve(t.check)
        res = res ::: retrieve(t.assign)
      })
    })
    res.toSet
  }
//}}}
}

def getIdStr(v1:Any,v2:Any):Int = {
//{{{
  def prefill(maxI:String,i:String):String = {var res=i;while(maxI.size>res.size) res = "0"+res;res}
  v1 match {
    case a:Automaton_Base => v2 match {
      case loc:Location => {
        val res = a.locations.indexOf(loc)
        assert(res!= -1)
        res
      }
      case _ => throw new AssertFail
    }
    case ac:Automaton_Composite => v2 match {
      case a:Automaton_Base => {
        val aS = retrieve_base_automata(ac)
        val i = aS.indexOf(a)
        assert(i!= -1)
        prefill((aS.size-1).toString,i.toString)
      }
      case Fork(c,l,r) => getIdStr(ac,l) + getIdStr(ac,r)
      case _ => throw new AssertFail
    }
    case _ => throw new AssertFail
  }
//}}}
}

def toStr(ac:Automaton_Composite,stringifier: Any => (String,String)):String = {
//{{{
  var res = ""

  retrieve_base_automata(ac).foreach(a => {
    stringifier((ac,a))._1
    locations.foreach(loc => {
      res += stringifier((ac,a,loc))._1
      if(l.evolve != None) res += stringifier('evolve,l.evolve.get)._1
      if(l.inv    != None) res += stringifier('inv   ,l.inv   .get)._1
      res += stringifier((ac,a,loc))._2
    })
    locations.foreach(loc => loc.transitions.foreach(t = {
      res += stringifier((ac,a,loc,t.to))._1
      if(l.check  != None) res += stringifier('check ,l.check )._1
      if(l.assign != None) res += stringifier('assign,l.assign)._1
      res += stringifier((ac,a,loc,t.to))._2
    }))
    stringifier((ac,a))._2
  })

  def traverse(ac_:Automaton_Composite):Unit = ac_ match {
    case Fork(c,ac_1,ac_2) => {
      traverse(ac_1)
      traverse(ac_2)
      res += stringifier(ac,c,ac_,ac_1,ac_2)._1
    }
    case Automaton_Base => Unit
  }
  traverse(ac)
  res
}
//}}}

class Automaton {
//{{{
  sealed abstract class Forb
  case class EndsEq(f:Formula   ,l:List[Automaton#Location]) extends Forb
  case class Choice(c:Connective,forbS:List[Automaton#Forb]) extends Forb

  def add_location():Automaton#Location = {val newL=new Location;locations=locations:+newL;newL}

  def size = locations.size

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

  def forb_to_composition():List(Automaton) = {
  //{{{
    (c
  //}}}
  }
//}}}
}

object Spaceex {
//{{{
  //TODO
  //-rewrite this termToStr -- make string converstion manually -- rewrite retrieve_varS
  //-seperate to string code and spaceex specific code
  object spaceexDeparse {
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

    def toSX(a:Automaton) = {
    //{{{
      //
      assert(spaceexDeparse.varS.length>0,"assumption that toSX would be called max one time apparently false")

      //only purpose of following paragraph is to set varS
      for(l <- a.locations)
      {
        spaceexDeparse(l.inv)
        spaceexDeparse(l.evolve)
        for(t <- l.transitions)
        {
          spaceexDeparse(t.check)
          spaceexDeparse(t.assign)
        }
      }

      def make_evolve_explicit(v: Any):List[(Fn,Term)] = v match
      {
        case l:List[(Fn,Term)] => {
          var varS_todo:Set[String] = spaceexDeparse.varS.toSet
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
        locations_str+= spaceexDeparse(l.inv,"invariant","    ","\n")
      //locations_str+= spaceexDeparse(l.evolve,"flow","    ","\n")
        locations_str+= spaceexDeparse(make_evolve_explicit(l.evolve),"flow","    ","\n")
        locations_str+= "  </location>\n"
        for(t <- l.transitions)
        {
          transitions_str+= "  <transition source=\""+id+"\" target=\""+t.to.id.toString()+"\">\n"
          transitions_str+= spaceexDeparse(t.check ,                                                                    "guard"     ,"    ","\n")
          transitions_str+= spaceexDeparse(t.assign,                                                                    "assignment","    ","\n")
        ////no assertion that var isendstate is already used
        //transitions_str+= spaceexDeparse(List((Fn("isendstate",Nil),Num((if(t.to.isEnd)Exact.one else Exact.zero)))),"assignment","    ","\n")
          transitions_str+= "  </transition>\n"
        }
      }

      var res = ""
      def xmlParam(v:String,t:String) = "  <param name=\""+v+"\" type=\""+t+"\" d1=\"1\" d2=\"1\" local=\"true\" dynamics=\"any\"/>\n"
      spaceexDeparse.varS.toSet.foreach((v: String) => res+=xmlParam(v,"real"))

      res+=locations_str
      res+=transitions_str

      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">\n"+"<component id=\"system\">\n"+res+"</component>\n</sspaceex>"
    //}}}
    }

    //spaceexDeparse required
    def str_sx(ac:Automaton_Composite):String = {
    //{{{
      def stringifier_sx(v: Any):String = {
      //{{{
        v match {
          case (ac:Automaton_Composite,c:Connective,ac0:Automaton_Composite,ac1:Automaton_Composite,ac2:Automaton_Composite) = {
            def bindStr(idStr:String):String = "<bind component=\""+idStr+"\" as=\""+INAME(idStr)+"\"></bind>"
            (bindStr(getIdStr(ac,ac1))+"\n"+bindStr(getIdStr(ac,ac2)),"")
          }
          case (ac:Automaton_Composite,a:Automaton_Base) => ("<component id=\""+getIdStr(ac,a)+"\">\n"+retrieve_varS(a).map(varStr => "<param name=\""+varStr+"\" type=\"real\" d1=\"1\" d1=\"2\" local=\"true\" dynamics=\"any\" controlled=\"false\">").mkString("\n")+"\n"),"\n</component>")
          case (ac:Automaton_Composite,a:Automaton_Base,loc:Location) =>
            ("<location id=\""+getIdStr(a,loc)+"\" name=\""+LNAME(getIdStr(a,loc))+"\">\n","\n</location>")
          case (ac:Automaton_Composite,a:Automaton_Base,from:Location,to:Location) =>
            ("<transition source=\""+getIdStr(a,from)+"\" target=\""+getIdStr(a,to)+"\">\n,"\n</transition>")
          case (type:Symbol,v:Any) => ("<"+(type.toString() drop 1)+">"+spaceexDeparse(v)+"</"(type.toString() drop 1)+">","")
          case _ => throw new AssertFail
        }
      //}}}
      }

      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">\n"+toStr(ac,stringifier_sx)+"\n</sspaceex>"
     //}}}
    }
    def str_graph(ac: Automaton_Composite):String = {
    //{{{
      //graphviz format
      def stringifier_graph(v: Any):String = {
      //{{{
        def getIdAbsolute(ac:Automaton_Composite,a:Automaton_Base,loc:Location) = getIdStr(ac,a)+"_"+getIdStr(a,loc)
        v match {
          case (ac:Automaton_Composite,c:Connective,ac0:Automaton_Composite,ac1:Automaton_Composite,ac2:Automaton_Composite) = {
            def getNodeId(ac_:Automaton_Composite) = ac_ match {
              case a:Automaton_Base => getIdAbsolute(ac,a,a.start)
              case Fork => getIdStr(ac,ac_)
            }
            (getIdStr(ac,ac0)+" [label=\""+c.toString+"]\n"+getNodeId(ac0)+"->"+getNodeId(ac1)+"\n"+getNodeId(ac0)+"->"+getNodeId(ac2),"")
          }
          case (ac:Automaton_Composite,a:Automaton_Base) => ("","")
          case (ac:Automaton_Composite,a:Automaton_Base,loc:Location) => {
            val locId = getIdAbsolute(ac,a,loc)
            val pre = locId+" [label=\""+locId

            val post = ""
            if(isEnd(a,loc)) post+= "\" shape=\"doublecircle"
            post+= "\"]\n"
            if(isStart(a,loc)) post+= "\nE->"+locId

            (pre,post)
          }
          case (ac:Automaton_Composite,a:Automaton_Base,from:Location,to:Location) =>
             ("\n"+getIdAbsolute(ac,a,from)+"->"+getIdAbsolute(ac,a,to)+" [label=\"" , "\"]")
          case (type:Symbol,v:Any) => (" "+(type.toString() drop 1)+":"+spaceexDeparse(v),"")
          case _ => throw new AssertFail
        }
      //}}}
      }
      "digraph hybrid_automata {\nE[label=\"\" shape=none]\n"+toStr(ac,stringifier_graph)+"}"
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

  private def spaceexize(ac:Automaton_Composite) = {
    retrieve_base_automata(ac).foreach(a => {
      var newLocations = a.locations
      a.locations.foreach({ loc => 
        if(loc.inv != None)
        {
          val inv_dnf = UTtil_Formula.DNFize(loc.inv.get)
          assert(inv_dnf.length>0)
          if(inv_dnf.length==1)
            loc.inv = Some(inv_dnf(0))
          else
          {
            for(i <- 0 to inv_dnf.length-1)
            {
              val newLoc = new Location(List(new Transition(loc)),loc.evolve,Some(inv_dnf(i)))
              loc.transitions = loc.transitions :+ new Transition(newLoc)
              newLocations = :+ newLoc
            }
            loc.inv = None
            loc.evolve = None
          }
        }
      })
      a.locations = newLocations
    })
  }

  private def toSpaceexAutomaton(a:Automaton):Unit =
  //{{{
  {
    for(l <- a.locations)
    {
      if(l.inv != None)
      {
      }
      for(t <- l.transitions)
      {
        if(t.check != None)
        {
          val check_dnf = UTtil_Formula.DNFize(t.check.get)
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
        val ac = toAutomaton(h)
        //println(Stringify.str_txt(ac))

        toSpaceexAutomaton(ac)

        Util.str2file("DLBanyan/_.dot",Stringify.str_graph(ac))
        //Util.str2file("DLBanyan/_.cfg",configFile("loc()==l"+a.start.id,spaceexDeparse(a.forb_to_formula)))
        Util.str2file("DLBanyan/_.xml",Stringify.str_sx(ac))

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
