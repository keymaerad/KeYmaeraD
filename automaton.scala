package DLBanyan

class TooWeak       (e:String)    extends Exception("no way found to support "+e)
class NotImplemented(e:String)    extends Exception(e)
class TODO          (e:String)    extends Exception(e)
class AssertFail    (e:String="") extends Exception(e)

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
      case Binop(Or ,f1,f2) => DNFize(f1) ::: DNFize(f2)
      case Binop(And,f1,f2) => {
        var res:List[Formula] = List()
          DNFize(f1).foreach(fleft => {
            DNFize(f2).foreach(fright => res = Binop(And,fleft,fright)::res)
          })
        res
      }
      case Atom(_) | True | False => List(g)
      case Modality(Box,_,_) => throw new Exception("should have been could before")
      case Binop(Iff,_,_) | Binop(Imp,_,_) | Not(_) | Quantifier(_,_,_,_) | Modality(Diamond,_,_) => throw new Exception("these classes should have been eliminted by normalize before")
    }
  //}}}
  }

  def isArithmetic(f:Formula):Boolean = {
  //{{{
    f match {
      case Modality(_,_,_) => false
      case Binop (c,f1,f2) => isArithmetic(f1) & isArithmetic(f2)
      case Quantifier(_,_,_,_) => throw new TODO("get rid of quantifiers")
      case _ => true
    }
  //}}}
  }
//}}}
}

class Location(var transitions : List[Transition]        = Nil,
               var evolve      : Option[List[(Fn,Term)]] = None,
               var inv         : Option[Formula]         = None
              )

class Transition(val to     : Location,
                 var check  : Option[Formula]          = None,
                 val assign : Option[List[(Fn, Term)]] = None
                )

sealed abstract class Automaton_Composite
  case class Automaton_Base(var locations : List[Location],
                            var start     : Location,
                            val ends      : List[Location],
                            val forb      : Formula = True
                           )                                                       extends Automaton_Composite
  case class Fork(c:Connective,left:Automaton_Composite,right:Automaton_Composite) extends Automaton_Composite

object aFcts {
  def toAutomaton(f: Formula):Automaton_Composite = {
  //{{{
    def seqAutomata(a1:Automaton_Base,a2:Automaton_Base):Automaton_Base = {
      a1.ends.foreach(end => end.transitions = end.transitions :+ new Transition(a2.start))
      Automaton_Base(a1.locations ::: a2.locations,a1.start,a2.ends)
    }
    def hpToAutomaton(hp: HP):Automaton_Base = {
    //{{{
      def transition_automaton(check:Option[Formula]=None,assign:Option[List[(Fn,Term)]]=None):Automaton_Base = {
        val end   = new Location
        val start = new Location(List(new Transition(end,check,assign)))
        Automaton_Base(List(start,end),start,List(end))
      }
      hp match {
        case Check(h:Formula) => transition_automaton(Some(h))
        case Assign(l)        => transition_automaton(None,Some(l))
        case Seq(p1: HP, p2: HP) => seqAutomata(hpToAutomaton(p1),hpToAutomaton(p2))
        case Evolve(derivs, h,_,_) => //derivs: List[(Fn,Term)], h: Formula
          val newLoc = new Location(Nil,Some(derivs),Some(h))
          Automaton_Base(List(newLoc),newLoc,List(newLoc))
        case Choose(p1: HP, p2: HP) =>
          val a1 = hpToAutomaton(p1)
          val a2 = hpToAutomaton(p2)
          val start = new Location(List(new Transition(a1.start),new Transition(a2.start)))
          Automaton_Base(start :: a1.locations ::: a2.locations,start,a1.ends ::: a2.ends)
        case Loop(p1: HP,_,_) =>
          val a1 = hpToAutomaton(p1)
          a1.ends.foreach(end => end.transitions = end.transitions :+ new Transition(a1.start))
          a1
        case _ => throw new TooWeak("automaton simulate * assignments and quantified assignments / diff eqS")
      }
    //}}}
    }

    if(Util_Formula.isArithmetic(f)) return hpToAutomaton(Check(f))

    val f_normalized = Util_Formula.normalize(f)

    f_normalized match {
      case Binop(c,f1,f2) => Fork(c,toAutomaton(f1),toAutomaton(f2))
      case Modality(Box,hp,phi) => {
        val phiAutomaton = toAutomaton(phi)
        phiAutomaton match {
          case a:Automaton_Base => seqAutomata(hpToAutomaton(hp),a)
          case _ => throw new TODO("subclass of formulas are simulate-able")
        }
      }
      case Modality(Diamond,_,_) => throw new TooWeak("Diamond modality")
      case _ => throw new Exception("this should have been catched by isArithmetic()")
    }
  //}}}
  }

  def isStart(a:Automaton_Base,loc:Location) = a.start == loc
  def isEnd  (a:Automaton_Base,loc:Location) = a.ends.indexOf(loc)!= -1

  def retrieve_base_automata(ac:Automaton_Composite):List[Automaton_Base] = ac match {
  //{{{
    case a:Automaton_Base => List(a)
    case Fork(c,l,r)               => retrieve_base_automata(l) ::: retrieve_base_automata(r)
  //}}}
  }

  def retrieve_varS(v:Any):Set[String] = v match {
  //{{{
    case Some(v1:Any) => retrieve_varS(v1)
    case None => Set()
    case Fork(_,l,r) => retrieve_varS(l) | retrieve_varS(r)
    case a:Automaton_Base => {
      var res:Set[String] = Set()
      a.locations.foreach(l => {
        res = res | retrieve_varS(l.evolve)
        res = res | retrieve_varS(l.inv)
        l.transitions.foreach(t => {
          res = res | retrieve_varS(t.check)
          res = res | retrieve_varS(t.assign)
        })
      })
      res
    }

    case t:Term => t match {
      case Fn(symbolStr:String,l:List[Term]) => {
        if(l.size==0)
          Set(symbolStr)
        else
          l.map(retrieve_varS).reduce(_|_)
      }
      case Num(_) => Set()
      case Var(_) => throw new AssertFail //never saw Var occur
    }
    case Tuple2(l,r) => retrieve_varS(l) | retrieve_varS(r)
    case l:List[_] => (l.map(retrieve_varS) ::: List(Set[String]())).reduce(_|_) // List().reduce => exception

    case f:Formula => f match {
      case Atom(R(_,terms:List[_])) => {
        assert(terms.length==2,"until now only relations with arity 2 used")
        terms.map(retrieve_varS).reduce(_|_)
        terms(0) match {
          case Fn(varName:String,l:List[_]) => {assert(l.size==0);Set(varName)}
          case _ => throw new AssertFail
        }
      }
      case Binop(_,f1,f2) => retrieve_varS(f1) | retrieve_varS(f2)
      case Not(f1) => retrieve_varS(f1)
      case True | False => Set()
      case Quantifier(_,_,_,_) | Modality(_,_,_) => throw new AssertFail
    }
    case _ => throw new AssertFail(v.asInstanceOf[AnyRef].getClass.getName())
  //}}}
  }

  def getIdStr(v1:Any,v2:Any):String = {
  //{{{
    def prefill(maxI:String,i:String):String = {var res=i;while(maxI.size>res.size) res = "0"+res;res}
    v2 match {
      case loc:Location => v1 match {
        case a:Automaton_Base => {
          val res = a.locations.indexOf(loc)
          assert(res!= -1)
          res.toString
        }
        case _ => throw new AssertFail
      }
      case ac_2:Automaton_Composite => v1 match {
        case ac:Automaton_Composite => ac_2 match {
          case a:Automaton_Base => {
            val aS = retrieve_base_automata(ac)
            val i = aS.indexOf(a)
            assert(i!= -1)
            prefill((aS.size-1).toString,i.toString)
          }
          case Fork(c,l,r) => getIdStr(ac,l) + getIdStr(ac,r)
        }
        case _ => throw new AssertFail
      }
      case _ => throw new AssertFail
    }

    /*
    v1 match {
      case a:Automaton_Base => v2 match {
        case loc:Location => {
          val res = a.locations.indexOf(loc)
          assert(res!= -1)
          res.toString
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
    */
  //}}}
  }

  def toStr(ac:Automaton_Composite,stringifier: Any => (String,String)):String = {
  //{{{
    var res = ""

    retrieve_base_automata(ac).foreach(a => {
      res += stringifier((ac,a))._1
      a.locations.foreach(loc => {
        res += stringifier((ac,a,loc))._1
        if(loc.evolve != None) res += stringifier(('evolve,loc.evolve.get))._1
        if(loc.inv    != None) res += stringifier(('inv   ,loc.inv   .get))._1
        res += stringifier((ac,a,loc))._2
      })
      a.locations.foreach(loc => loc.transitions.foreach(t => {
        res += stringifier((ac,a,loc,t.to))._1
        if(t.check  != None) res += stringifier(('check ,t.check ))._1
        if(t.assign != None) res += stringifier(('assign,t.assign))._1
        res += stringifier((ac,a,loc,t.to))._2
      }))
      res += stringifier((ac,a))._2
    })

    def traverse(ac_x:Automaton_Composite):Unit = ac_x match {
      case Fork(c,ac_1,ac_2) => {
        traverse(ac_1)
        traverse(ac_2)
        res += stringifier(ac,c,ac_x,ac_1,ac_2)._1
      }
      case Automaton_Base(_,_,_,_) => Unit
    }
    traverse(ac)
    res
  //}}}
  }
}

object Spaceex {
//{{{
  //TODO
  //-rewrite this termToStr -- make string converstion manually
  //-seperate to string code and spaceex specific code
  object spaceexDeparse {
  //{{{
    //assumptions:
    //-char . is only used for Fn(_,Nil) by docOfTerm
    //-char . is only used for forall/exists by docOfFormula (or by calling docOfTerm)
    //-always a space between . and forall/exists
    //-Printing fcts make returns char . only by calling docOfTerm or docOfFormula

    def connectiveToStr(c:Connective):String = c match {
      case Or  => "|"
      case And => "&"
      case Imp => "=>"
      case Iff => "<=>"
    }

    def apply(v:Any, sep:String="' == ", isConfig:Boolean=false):String = {

      def formulaToStr(f:Formula):String = {
      //{{{
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
          def escapeXml(s:String):String = if(isConfig) s else s.replaceAll("<","&lt;").replaceAll(">","&gt;")
          escapeXml(s.replaceAll("0 -","-").replaceAll("([^<>!=])=","$1==").replaceAll("\\.",""))
         }
       //}}}

        val sw = new java.io.StringWriter()
        val d = Printing.docOfTerm(tm)
        d.format(70, sw)
        val res = sw.toString
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
                doIt(termToStr(x)+sep+termToStr(tm))
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

      doIt(v)
    }
  //}}}
  }

  object Stringify {
  //def todel(idStr:String) = idStr+"we"
    def INAME(idStr:String) = "i_"+idStr
    def LNAME(idStr:String) = "l" +idStr

    //spaceexDeparse required
    def str_sx(ac:Automaton_Composite):String = {
    //{{{
      def stringifier_sx(v: Any):(String,String) = {
      //{{{
        v match {
          case (ac:Automaton_Composite,c:Connective,ac0:Automaton_Composite,ac1:Automaton_Composite,ac2:Automaton_Composite) => {
            def bindStr(idStr:String):String = "<bind component=\""+idStr+"\" as=\""+INAME(idStr)+"\"></bind>"
            (bindStr(aFcts.getIdStr(ac,ac1))+"\n"+bindStr(aFcts.getIdStr(ac,ac2)),"")
          }
          case (ac:Automaton_Composite,a:Automaton_Base) => ("\n<component id=\""+aFcts.getIdStr(ac,a)+"\">\n"+aFcts.retrieve_varS(a).map(varStr => "  <param name=\""+varStr+"\" type=\"real\" d1=\"1\" d2=\"1\" local=\"true\" dynamics=\"any\" controlled=\"false\"/>").mkString("\n"),"\n</component>")
          case (ac:Automaton_Composite,a:Automaton_Base,loc:Location) =>
            ("\n  <location id=\""+aFcts.getIdStr(a,loc)+"\" name=\""+LNAME(aFcts.getIdStr(a,loc))+"\">","\n  </location>")
          case (ac:Automaton_Composite,a:Automaton_Base,from:Location,to:Location) =>
            ("\n  <transition source=\""+aFcts.getIdStr(a,from)+"\" target=\""+aFcts.getIdStr(a,to)+"\">","\n  </transition>")
          case (typi:Symbol,v:Any) => ("\n    <"+(typi.toString() drop 1)+">"+spaceexDeparse(v,(if(typi=='assign) " := " else "' == "))+"</"+(typi.toString() drop 1)+">","")
          case _ => throw new AssertFail
        }
      //}}}
      }

      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<sspaceex xmlns=\"http://www-verimag.imag.fr/xml-namespaces/sspaceex\" version=\"0.2\" math=\"SpaceEx\">"+aFcts.toStr(ac,stringifier_sx)+"\n</sspaceex>"
     //}}}
    }
    def str_graph(ac: Automaton_Composite):String = {
    //{{{
      //graphviz format
      def stringifier_graph(v: Any):(String,String) = {
      //{{{
        def getIdAbsolute(ac:Automaton_Composite,a:Automaton_Base,loc:Location) = "c"+aFcts.getIdStr(ac,a)+"l"+aFcts.getIdStr(a,loc)
        v match {
          case (ac:Automaton_Composite,c:Connective,ac0:Automaton_Composite,ac1:Automaton_Composite,ac2:Automaton_Composite) => {
            def getNodeId(ac_x:Automaton_Composite) = ac_x match {
              case a:Automaton_Base => getIdAbsolute(ac,a,a.start)
              case Fork(_,_,_) => aFcts.getIdStr(ac,ac_x)
            }
            (aFcts.getIdStr(ac,ac0)+" [label=\""+c.toString+"]\n"+getNodeId(ac0)+"->"+getNodeId(ac1)+"\n"+getNodeId(ac0)+"->"+getNodeId(ac2),"")
          }
          case (ac:Automaton_Composite,a:Automaton_Base) => ("","")
          case (ac:Automaton_Composite,a:Automaton_Base,loc:Location) => {
            val locId = getIdAbsolute(ac,a,loc)
            val pre = "\n"+locId+" [label=\""

            var post = ""
            if(aFcts.isEnd(a,loc)) post+= "\" shape=\"doublecircle"
            post+= "\"]"
            if(aFcts.isStart(a,loc)) post+= "\nE->"+locId

            (pre,post)
          }
          case (ac:Automaton_Composite,a:Automaton_Base,from:Location,to:Location) =>
             ("\n"+getIdAbsolute(ac,a,from)+"->"+getIdAbsolute(ac,a,to)+" [label=\"" , "\"]")
          case (typi:Symbol,v:Any) => (" "+(typi.toString() drop 1)+":"+spaceexDeparse(v),"")
          case _ => throw new AssertFail
        }
      //}}}
      }
      "digraph hybrid_automata {\nE[label=\"\" shape=none]"+aFcts.toStr(ac,stringifier_graph)+"}"
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

  //getIdStr(ac,ac) is the system component
  def getIdStr_cfg(ac:Automaton_Composite,a:Automaton_Base) = if(aFcts.getIdStr(ac,ac)==aFcts.getIdStr(ac,a)) "" else aFcts.getIdStr(ac,a)

  private def init(ac:Automaton_Composite):String = {
  //{{{
    var init_constraints:List[String] = Nil
    var freeVars:List[(Automaton_Base,Set[String])] = Nil
    aFcts.retrieve_base_automata(ac).foreach(a => {
      init_constraints = init_constraints :+ "loc("+getIdStr_cfg(ac,a)+")==l"+aFcts.getIdStr(a,a.start)
      freeVars = freeVars :+ (a,aFcts.retrieve_varS(a))
    })
    for(i <- 1 to freeVars.length-1)
      for(j <- i to freeVars.length-1)
        init_constraints = init_constraints ::: freeVars(i)._2.intersect(freeVars(j)._2).map(varStr => aFcts.getIdStr(ac,freeVars(i)._1)+"."+varStr+"=="+aFcts.getIdStr(ac,freeVars(j)._1)+"."+varStr).toList
    init_constraints.mkString(" & ")
  //}}}
  }
  private def forb(ac:Automaton_Composite):String = ac match {
  //{{{
    case Fork(c,ac1,ac2) => "( "+forb(ac1)+" "+spaceexDeparse.connectiveToStr(c)+" "+forb(ac2)+" )"
    case a:Automaton_Base => "("+a.ends.map(end => "loc("+getIdStr_cfg(ac,a)+")==l"+aFcts.getIdStr(a,end)).mkString(" | ")+") & "+spaceexDeparse(a.forb)
  //}}}
  }

  private def spaceexize(ac:Automaton_Composite):Unit = {
  //{{{
    aFcts.retrieve_base_automata(ac).foreach(a => {
      var newLocations = a.locations
      a.locations.foreach({ loc => 
        if(loc.inv != None)
        {
          val inv_dnf = Util_Formula.DNFize(loc.inv.get)
          assert(inv_dnf.length>0)
          if(inv_dnf.length==1)
            loc.inv = Some(inv_dnf(0))
          else
          {
            for(i <- 0 to inv_dnf.length-1)
            {
              val newLoc = new Location(List(new Transition(loc)),loc.evolve,Some(inv_dnf(i)))
              loc.transitions = loc.transitions :+ new Transition(newLoc)
              newLocations = newLocations :+ newLoc
            }
            loc.inv    = None
            loc.evolve = None
          }
        }

        var newTransitions = loc.transitions
        loc.transitions.foreach(t => {
          if(t.check != None)
          {
            val check_dnf = Util_Formula.DNFize(t.check.get)
            assert(check_dnf.length>0)
            t.check = Some(check_dnf(0))
            for(i <- 1 to check_dnf.length-1)
              newTransitions = newTransitions :+ new Transition(t.to,Some(check_dnf(i)),t.assign)
          }
        })
        loc.transitions = newTransitions
      })
      a.locations = newLocations

      //explicit evolve -- for uncontrolled vars -- for now all are uncontrolled
      a.locations.foreach(loc => {
        if(loc.evolve == None) loc.evolve = Some(Nil)
        assert(aFcts.retrieve_varS(loc.evolve).size==aFcts.retrieve_varS(loc.evolve).intersect(aFcts.retrieve_varS(a)).size)
        aFcts.retrieve_varS(a).diff(aFcts.retrieve_varS(loc.evolve)).foreach(varStr =>
          loc.evolve = Some(loc.evolve.get :+ (Fn(varStr,Nil),Num(Exact.zero)))
        )
      })

      //add self loop start location for composition
      val newLoc = new Location
      newLoc.transitions = List(new Transition(newLoc),new Transition(a.start))
      a.locations = newLoc :: a.locations
      a.start     = newLoc
    })
  }
  //}}}

  def configFile(init:String,forbidden:String,system:String):String = {
    //{{{
    var res=""
    res+="initially = \""+init+"\"\n"
    res+="forbidden = \""+forbidden+"\"\n"
    res+="system = \""+system+"\"\n"
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
        val ac = aFcts.toAutomaton(h)
        //println(Stringify.str_txt(ac))

        Util.str2file("DLBanyan/_.dot",Stringify.str_graph(ac))

        spaceexize(ac)

        Util.str2file("DLBanyan/_.cfg",configFile(init(ac),forb(ac),aFcts.getIdStr(ac,ac)))
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
