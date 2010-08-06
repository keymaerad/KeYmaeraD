package DLBanyan


object Tactics {

  import Nodes._
  import TreeActions._
  import RulesUtil._
  import Rules._


  abstract class Tactic(name: String) extends ((OrNode) =>  Unit) {
    override def toString: String = {
      name
    }
  }



  def usehints(pos: Position): Tactic = new Tactic("usehints") {
    def apply(nd: OrNode ) = lookup(pos,nd.goal) match {
      case Box(Loop(hp, True, inv_hints), phi) => 
        val rules = inv_hints.map(loopInduction)
        rules.map(r => applyrule(nd, pos, r))
      case Box(Evolve(derivs,h,inv_hints,sols), phi) =>
        val rules = inv_hints.map(diffStrengthen)
        rules.map(r => applyrule(nd, pos, r))
      case _ => ()
    }
  }


  val hpeasy = List(seq, chooseRight, checkRight, 
                    assignRight, assignAnyRight,
                    diffClose
                  )

  val needhints = List(loopInduction, diffStrengthen)

  // how do tactics compose?

  val hpeasyT : Tactic = new Tactic("hpeasy") {
    def apply(nd: OrNode) = nd.goal match {
      case Sequent(c,List(s)) =>
        // try all the box hp easy rules
        val pos = RightP(0)
        hpeasy.map(r => applyrule(nd,pos,r))
        usehints(pos)
      case _ => 
    }

  }

}
