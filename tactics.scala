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
      case Box(Repeat(hp, True, inv_hints), phi) => 
        val rules = inv_hints.map(loopInduction)
        rules.map(r => applyrule(nd, pos, r))
/*      case Box(Evolve(derivs,h,inv_hints,sols), phi) =>
        val rules = inv_hints.map(diffInduction)
        rules.map(r => applyrule(nd, pos, r))
*/
      case _ => ()
    }

  }
}
