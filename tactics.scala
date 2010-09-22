package DLBanyan


object Tactics {

  import Nodes._
  import TreeActions._
  import RulesUtil._
  import Rules._

  
  // A tactic return a list of the new open leaves that it spawns.

  abstract class Tactic(name: String) extends ((OrNode) =>  List[NodeID]) {
    override def toString: String = {
      name
    }
  }



  def usehints(pos: Position): Tactic = new Tactic("usehints") {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Box(Loop(hp, True, inv_hints), phi) => 
        val rules = inv_hints.map(loopInduction)
        rules.map(r => applyrule(nd, pos, r)).flatten.flatten
      case Box(Evolve(derivs,h,inv_hints,sols), phi) =>
        val inv_rules = inv_hints.map(diffStrengthen)
        val inv_res = inv_rules.map(r => applyrule(nd, pos, r)).flatten.flatten
        val sol_rule = diffSolve(sols)
        val sol_res = applyrule(nd,pos,sol_rule) match {
          case None => Nil
          case Some(lst) => lst
        }
        sol_res ++ inv_res
        
      case _ => Nil
    }
  }


  val hpeasy = List(seq, chooseRight, checkRight, 
                    assignRight, assignAnyRight,
                    diffClose
                  )

  val needhints = List(loopInduction, diffStrengthen)


  def composeT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("compose " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) = {
        val newnds = t1(nd)
        newnds.map(c => 
          {getnodethen(c,gotonode _);
           hereNode match {
                case ornd@OrNode(_,_) =>
                  t2(ornd)
                case _ => Nil
              }}).flatten 
      }

    }


  val hpeasyT : Tactic = new Tactic("hpeasy") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(c,List(s)) =>
        // try all the box hp easy rules
        val pos = RightP(0)
        val nds1 = hpeasy.map(r => applyrule(nd,pos,r)).flatten.flatten
        val nds2 = usehints(pos)(nd)
        nds1 ++ nds2
      case _ => Nil
    }
  }


  def repeatT(t: Tactic) : Tactic = new Tactic("repeat " + t.toString) {
    def apply(nd: OrNode) = {
      val newnds = t(nd)
      if (newnds.length == 0) List(nd.nodeID)
      else newnds.map( 
        c => {getnodethen(c,gotonode _);
              hereNode match {
                case ornd@OrNode(_,_) =>
                  apply(ornd)
                case _ => Nil
              }
            }).flatten

    }

  }



  val substT : Tactic = new Tactic("substitute") {
    def apply(nd: OrNode) = nd.goal match {
      case sq@Sequent(c,s) =>

        var foundone = false;
        var res: List[NodeID] = Nil;
      
        for (i <- c.indices) {
          if(foundone == false){
            val pos = LeftP(i)
            substitute.apply(pos)(sq) match {
              case Some(_) =>
                res = applyrule(nd,pos,substitute) match { case Some(lst) => lst
                                                          case None => Nil};
                foundone = true;
                ()
              case None => 
                ()
            }
          }
        }

        res

      case _ => Nil
    }
  }


  def arithT : Tactic = new Tactic("arithmetic") {
    def apply(nd: OrNode): List[NodeID] = {
      submitproc(nd, "math")
      Nil
    }

  }


  val beta = List(andRight, orLeft)

/*
  val betaT : Tactic = new Tactic("beta") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(c,s) =>

        var foundone = false;
        var res: List[NodeID] = Nil;
      
        for (i <- c.indices) {
          if(foundone == false){
            val pos = LeftP(i)
            substitute.apply(pos)(sq) match {
              case Some(_) =>
                res = applyrule(nd,pos,substitute) match { case Some(lst) => lst
                                                          case None => Nil};
                foundone = true;
                ()
              case None => 
                ()
            }
          }
        }

        res


        // try all the  rules
        val pos = RightP(0)
        val nds1 = hpeasy.map(r => applyrule(nd,pos,r)).flatten.flatten
        val nds2 = usehints(pos)(nd)
        nds1 ++ nds2
      case _ => Nil
    }
  }
*/

  val alleasyT: Tactic = composeT(repeatT(hpeasyT),
                                  composeT(repeatT(substT),
                                           arithT))


}
