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
        val rules = inv_hints.map(diffStrengthen)
        rules.map(r => applyrule(nd, pos, r)).flatten.flatten
      case _ => Nil
    }
  }


  val hpeasy = List(seq, chooseRight, checkRight, 
                    assignRight, assignAnyRight,
                    diffClose
                  )

  val needhints = List(loopInduction, diffStrengthen)

/*
  def composeT(t1: Tactic, t2: Tactic) : Tactic = 
    new Tactic("compose " + t1.toString + "," + t2.toString) {
      def apply(nd: OrNode) = {
        val newnds = t1(nd)
        newnds.map(c => t2(c)).flatten // need to make them ornodes
      }

    }
  */

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
        c => {gotonode(c);
              hereNode match {
                case ornd@OrNode(_,_) =>
                  apply(ornd)
                case _ => Nil
              }
            }).flatten

    }

  }


}
