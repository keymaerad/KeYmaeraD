package DLBanyan


import scala.text._
import scala.text.Document._


object Printing {

  def docOfList(lst:List[Document], sep: Document) : Document = lst match {
    case Nil => DocNil
    case x:: Nil => x
    case x::xs => x :: sep ::  docOfList(xs,sep)
  }

  
  def docOfTerm(tm: Term): Document = tm match {
    case Var(x) =>
      Document.text(x)
    case Fn(f, List(x,y)) if List("+","-","*", "/", "^").contains(f) =>
      text("(") :: docOfTerm(x) :: "+" :: docOfTerm(y) :: text(")")
    case Fn(f, args) =>
      Document.text(f) :: "(" :: 
        docOfList(args.map(docOfTerm), text(",")) :: text(")")
    case Num(n) =>
      Document.text(n.toString)
  }

  def docOfPred(p: Pred): Document = p match {
    case R(r,List(t1,t2)) if List("=", "<", ">", "<=", ">=", "<>"). contains(r) =>
      docOfTerm(t1) :: text(r) :: docOfTerm(t2)
    case R(r, ts)  =>
      text(r) :: text("(") ::
        docOfList(ts.map(docOfTerm), text(",")) :: text(")")
  }


  def docOfFormula(fm: Formula): Document = fm match {
    case True => text("true")
    case False => text("false")
    case Atom(p) => docOfPred(p)
    case And(fm1,fm2) => 
      text("(") :: docOfFormula(fm1) :: text("&") :: 
        docOfFormula(fm2) :: text(")")
    case Or(fm1,fm2) => 
      text("(") :: docOfFormula(fm1) :: text("|") :: 
        docOfFormula(fm2) :: text(")")
    case Imp(fm1,fm2) => 
      text("(") :: docOfFormula(fm1) :: text("==>") :: 
        docOfFormula(fm2) :: text(")")
    case Iff(fm1,fm2) => 
      text("(") :: docOfFormula(fm1) :: text("<=>") :: 
        docOfFormula(fm2) :: text(")")
    case Forall(x,fm) => 
      text("forall ") :: text(x) :: text(".") ::
          text("(") :: docOfFormula(fm) :: text(")")
    case Exists(x,fm) => 
      text("exists ") :: text(x) :: text(".") ::
          text("(") :: docOfFormula(fm) :: text(")")
    case Box(h,fm) =>
      text("[") :: docOfHP(h) :: text("]") :: docOfFormula(fm)
    case Diamond(h,fm) =>
      text("<") :: docOfHP(h) :: text(">") :: docOfFormula(fm)
  }


  def docOfHP(h: HP) : Document = h match {
    case Assign(x,tm) => 
     text(x) :: text(":=") :: docOfTerm(tm)
    case AssignAny(x) =>
     text(x) :: text(":= *")
    case Check(fm) =>
      text("?") :: docOfFormula(fm)
    case Seq(h1,h2) =>
      docOfHP(h1) :: text(";") :/: docOfHP(h2)
    case Choose(h1,h2) =>
      text("(") :: docOfHP(h1) :: text(")") :: 
          text("++") :/: text("(") :: docOfHP(h2) :: text(")")
    case Repeat(h, inv, hnts) =>
      text("{") :: docOfHP(h) :: text("}*")
    case Evolve(derivs, reg, hnts, sols) =>
      text("{") :: 
       docOfList(derivs.map(docOfDeriv), text(",")) ::
       text(";") ::
       docOfFormula(reg) :: 
       text("}")
  }


  def docOfDeriv(pr: (String,Term )) : Document = {
    text(pr._1 +"'") :: text(" = ") :: docOfTerm(pr._2)
  }

  def docOfSequent(sq: Sequent) : Document = sq match {
    case Sequent(c,s) =>
      docOfList(c.map(docOfFormula), DocCons(text(","), DocBreak)) :/:
       text("|-") ::
       docOfList(s.map(docOfFormula), DocCons(text(","), DocBreak))
  }


  def assoc[A,B](k: A, al: List[(A,B)]): Option[B] = al match {
    case (a,b) :: rest =>
      if( k == a ) Some(b)
      else assoc(k, rest)
    case Nil => None
  }

/*
  type NodeLogEntry = (String, String, String)
  type NodeAttribute = (String, String)
  type NodeRecord = (String, List[NodeAttribute], List[NodeLogEntry])


  abstract class DotType
  case class DotOne() extends DotType
  case class DotTwo(tm: Int) extends DotType
  case class DotThree() extends DotType

  class TreeData()  {
    var nodes: List[NodeRecord] = Nil
    var edges: List[(String,String)] = Nil

    
    val remoteNode = "remote"
    val unknownNode = "unknown"

    def addNode(nr: NodeRecord) : Unit = {
      nodes = nr:: nodes
    }

    def addEdge( nd1: String, nd2: String) : Unit = {
      edges = (nd1,nd2):: edges
    }

    def nodeString(): String = {
      val sb = new StringBuilder()
      for((nd,prs,log) <- nodes) {
        sb.append(nd)
        sb.append(" {\n")
        for((k,v)<- prs) {
          sb.append(k + " = " +  v + " \n")
        }
	sb.append("}\n{\n")
	for((w,c,t)<-log) {
	  sb.append(w + "," + c + "," +t + "\n")
	}
        sb.append("}\n")
      }
      sb.toString()
    }

   def nodeTiming(): String = {
     val sb = new StringBuilder()
     //println("node count: " + nodes.length)
     for((nd,prs,log) <- nodes) {
       //println("in node: " + nd + "with log length" + log.length)
       for((w,c,t)<-log) {
         sb.append(w + "," + c + "," + t + "\n")
       }
     }
     sb.toString()
   }




    def nodeDot1(): String = {
      val sb = new StringBuilder()
      for(e <- nodes) {
        val (nd,prs,log) = e
        sb.append(nd)
        sb.append("[")
        assoc("color", prs) match{
          case Some(col) => sb.append("color=" 
                                      + col)
          case None => sb.append("color = black")
        }
        assoc("time", prs) match {
          case Some(tm) => sb.append(",label = \""+ nd
                                     +" time = " + tm + "\"")
          case None =>
        }
        assoc("shape", prs) match {
          case Some(sh) => sb.append(",shape=" + sh)
          case None =>
        }
        sb.append(",style=filled]\n")
      }
      sb.toString()
    }

    def nodeDot2(t:Int): String = {
      val sb = new StringBuilder()
      for(e <- nodes) {
        val (nd,prs,log) = e
        sb.append(nd)
        sb.append("[")
        assoc("color", prs) match{
          case Some(col) => sb.append("color=" 
                                      + col)
          case None => sb.append("color = black")
        }
        assoc("shape", prs) match {
          case Some(sh) => sb.append(",shape=" + sh)
          case None =>
        }
        assoc("time", prs) match {
          case Some(tm) => 
            val tm1 = tm.split(" ")(0)
            val sz: Double = Math.sqrt(( 300.0 * Integer.parseInt(tm1)) / (t ))
            sb.append(",width = " + sz + ", height=" + sz)
          case None =>
        }
        sb.append(",label=\"\",style=filled]\n")
      }
      sb.toString()
    }


    def nodeDot3(): String = {
      val sb = new StringBuilder()
      for(e <- nodes) {
        val (nd,prs,log) = e
        sb.append(nd)
        sb.append("[")
        assoc("color", prs) match{
          case Some(col) => sb.append("color=" 
                                      + col)
          case None => sb.append("color = black")
        }
        assoc("label", prs) match {
          case Some(lb) => sb.append(",label = \"" + lb + "\"")
          case None =>
        }
/*
        assoc("shape", prs) match {
          case Some(sh) => sb.append(",shape=" + sh)
          case None =>
        }
*/
        sb.append("]\n")
      }
      sb.toString()
    }


    def edgeString(): String = {
      val sb = new StringBuilder()
      for((nd1,nd2)<- edges) {
        sb.append(nd1 + " " + nd2 + "\n")
      }
      sb.toString()
    }

    def edgeDot(): String = {
      val sb = new StringBuilder()
      for((nd1,nd2)<- edges) {
        sb.append(nd1 + " -> " + nd2 + "\n")
      }
      sb.toString()
    }


 
    override def toString(): String = {
      val sb = new StringBuilder()
      sb.append("nodes {\n")
      sb.append(nodeString())
      sb.append("}\nedges {\n")
      sb.append(edgeString())
      sb.append("}\n")
      sb.toString()
    }

    def toDot(t: DotType): String = {
      val sb = new StringBuilder()
      sb.append("digraph {\n")
      t match {
        case DotOne() =>
          sb.append(nodeDot1())
        case DotTwo(t) =>
          sb.append(nodeDot2(t))
        case DotThree() =>
          sb.append(nodeDot3())
      }
      sb.append(edgeDot())
      sb.append("}\n")
      sb.toString()
    }

    def convertLog(log:List[LogData]): List[NodeLogEntry] = {
      var list:List[NodeLogEntry] = Nil
      for(i<-log.indices) {
        list = list ::: List((log(i).worker, log(i).count.toString, log(i).time.toString))
      }
      list
    }
        

    def addTreeNode(nd:TreeNode, mainBranch: Boolean): Unit = {
      addNode((nd.nodeID.toString, 
               List(("label", nd.toString),
                    ("time", nd.timeSpentHere.toString),
                    ("status", nd.status.toString),
                    ("tickets", nd.checkTickets().toString ),
                    ("color", if(mainBranch) nd.colorMain else nd.color),
                    ("shape", nd.shape)),
	       convertLog(nd.workLog.remove(l => l.worker == ""))))
      for(c <- nd.children)  BanyanPrivate.nodeMap.get(c) match {
        case Some(NodeHere(nd1)) =>
          addEdge(nd.nodeID.toString, nd1.nodeID.toString)
        case Some(NodeThere(hst,id)) => 
          addEdge(nd.nodeID.toString, remoteNode)
        case None =>
          addEdge(nd.nodeID.toString, unknownNode)
      }
      for(c <- nd.children) {
        BanyanPrivate.nodeMap.get(c) match{
          case Some(NodeHere(nd1)) =>
            val mb = if(mainBranch && nd1.status == Returned()
                       && nd1.mainBranch == true) 
              true
              else false
            addTreeNode(nd1, mb)
          case Some(NodeThere(hst,id)) => 
            addNode(remoteNode, Nil, Nil)
          case None => 
            addNode(unknownNode, Nil, Nil)
        }
      }
    }
  

  }



 //  parsing of data files. 

 def matchLine(ln: String, mtch: List[String])
  : Boolean = {
     val wa = ln.split("( )+").toList
     if(wa == mtch){
       true
     } else {
       false
     }
  }


 def parseAttribute(ln: String)
  : Option[NodeAttribute] =  {
      val la = ln.split(" = ", 2)
      if(la.length == 2){
        Some((la(0), la(1)))
      }else{
        None
      }
  }

 def parseLogEntry(ln: String)
  : Option[NodeLogEntry] =  {
      val la = ln.split(",", 3)
      if(la.length == 3){
        Some((la(0), la(1), la(2)))
      }else{
        None
      }
  }


 def parseAttributes(inp: List[String])
  : (Option[List[NodeAttribute]], List[String]) = inp match {
    case Nil =>
      (None, Nil)
    case (ln::lns) =>
      parseAttribute(ln) match {
        case None =>
          if (matchLine(ln, List("}")) ){
            (Some(Nil), lns)
          } else {
            throw new Error("parse error")
          }
        case  Some( (k,v) ) =>
          val ( restAt,restLns) = parseAttributes(lns)
          restAt match {
            case None =>
              (None, inp)
            case Some(kvs) =>
              (Some((k,v):: kvs), restLns)
          }
      }

  }

 def parseLogEntries(inp: List[String])
  : (Option[List[NodeLogEntry]], List[String]) = inp match {
    case Nil =>
      (None, Nil)
    case (ln::lns) =>
      parseLogEntry(ln) match {
        case None =>
          if (matchLine(ln, List("}")) ){
	    (Some(Nil), lns)
	  } else {
	    throw new Error("parse error log data")
	  }
	case Some( (w,c,t) ) =>
	  val ( restAt, restLns) = parseLogEntries(lns)
	  restAt match {
	    case None =>
	      (None, inp)
	    case Some(wcts) =>
	      (Some((w,c,t):: wcts), restLns)
	  }
      }
  }

 def parseNodeRecord(inp: List[String])
  :(Option[NodeRecord], List[String]) = inp match {
    case Nil =>
      (None, Nil)
    case (ln::lns) =>
      val la = ln.split("( )+")
      if (la.length == 2 && la(1) == "{") {
        val (mbe_atts, intermed) = parseAttributes(lns)
	val (mbe_log, rest) = intermed match {
	  case Nil => (None, Nil)
	  case (lb::lbs) =>
	    if(lb == "{") {
	      parseLogEntries(lbs)
	    } else {
	      (None, intermed)
	    }
	}     
	mbe_atts match {
          case None => 
	    mbe_log match {
	      case None => (None, inp)
	      case Some(logs) => (Some(la(0), Nil, logs), rest)  
            }
          case Some(atts) => 
	    mbe_log match {
	      case None => (Some(la(0), atts, Nil), rest)
	      case Some(logs) => (Some(la(0), atts, logs), rest)
            }
	}
      } else {
        (None, inp)
      }
  }

 def parseNodeRecords(inp: List[String])
  : (Option[List[NodeRecord]], List[String]) =
      parseNodeRecord(inp) match {
        case (None, rest) =>
          if (matchLine(inp.head, List("}")) ){
            (Some(Nil), inp.tail)
          } else {
            throw new Error("parse error")
          }
        case  (Some( nr ), restLns) =>
          val ( restRec, restLns1) = parseNodeRecords(restLns)
          restRec match {
            case None =>
              (None, inp)
            case Some(nrs) =>
              (Some(nr :: nrs), restLns1)
          }
      }

  



 def parseEdge(ln: String)
  : Option[(String,String)] =  {
      val la = ln.split("( )+", 2)
      if(la.length == 2){
        Some((la(0), la(1)))
      }else{
        None
      }
  }



 def parseEdges(inp: List[String])
  : (Option[List[(String,String)]], List[String]) = inp match {
    case Nil =>
      (None, Nil)
    case (ln::lns) =>
      parseEdge(ln) match {
        case None =>
          if (matchLine(ln, List("}")) ){
            (Some(Nil), lns)
          } else {
            throw new Error("parse error")
          }
        case  Some( ed ) =>
          val ( restEds,restLns) = parseEdges(lns)
          restEds match {
            case None =>
              (None, inp)
            case Some(eds) =>
              (Some(ed :: eds), restLns)
          }
      }

  }


  

 def parseData(lines: List[String]): Option[TreeData] = {
   val td = new TreeData()
   lines match {
     case Nil =>
       None
     case ln::lns => 
       if(  matchLine(ln, List("nodes", "{"))) {
         val (mbe_nrs, restLns ) = parseNodeRecords(lns)
         mbe_nrs match {
           case None => None
           case Some(nrs) => 
             td.nodes = nrs
             restLns match {
               case Nil =>
                 Some(td)
               case ln1::lns1 =>
                 if ( matchLine(ln1, List("edges", "{"))){
                   val (mbe_eds, restLns1) = parseEdges(lns1)
                   mbe_eds match {
                     case None => None
                     case Some(eds) => 
                       td.edges = eds
                       Some(td)
                   }
                 } else {
                   None
                 }
             }
         }          
       } else {
         None
       }
    
   }

 }


  def main(args: Array[String]): Unit = {
    System.err.println("printing says: hello world")
    
    var opts = new org.apache.commons.cli.Options();
    opts.addOption("f", true, "file with data");
    opts.addOption("t", true, "draw proportional to time")
    opts.addOption("n", false, "write names of goals")
    opts.addOption("m", false, "collect node timing info")

    var parser = new org.apache.commons.cli.GnuParser();
    val cmd = parser.parse( opts, args);

    if (!cmd.hasOption("f")) {
      println("Forgot to supply filename. (use -f). Quitting.")
      System.exit(0);
    }


    val inp1 = 
      io.Source.fromFile(cmd.getOptionValue("f")).getLines.toList

    val inp = inp1.map(x => x.substring(0,x.length - 1))

    if(cmd.hasOption("m")) {
      parseData(inp) match {
        case None =>
	  println("no parse")
	case Some(td) =>
	  println(td.nodeTiming())
      }
      System.exit(0);
    }

    parseData(inp) match {
      case None =>
        println("no parse")
      case Some(td) =>
        if(cmd.hasOption("n")){
          println(td.toDot(DotThree()))
        } 
        else {
          if(!cmd.hasOption("t")){ 
            println(td.toDot(DotOne()))
          } 
          else {
           println(td.toDot(DotTwo(Integer.parseInt(cmd.getOptionValue("t")) )))
          }
        }
    }

    

  }

*/

}

