package DLBanyan

abstract class Term
case class Var(s: String) extends Term
case class Fn(f: String, ps: List[Term]) extends Term
case class Num(n: Exact.Num) extends Term

abstract class Pred
case class R(r: String, ps: List[Term]) extends Pred


// first order formula
abstract class FOFormula
case object True extends FOFormula
case object False extends FOFormula
case class Atom(p: Pred) extends FOFormula
case class Not(f: FOFormula) extends FOFormula
case class And(f1: FOFormula, f2: FOFormula) extends FOFormula
case class Or(f1: FOFormula, f2: FOFormula) extends FOFormula
case class Imp(f1: FOFormula, f2: FOFormula) extends FOFormula
case class Iff(f1: FOFormula, f2: FOFormula) extends FOFormula
case class Exists(v: String, f: FOFormula) extends FOFormula
case class Forall(v: String, f: FOFormula) extends FOFormula

abstract class HP
case class Assign(s: String, v: Term) extends HP
case class AssignAny(s: String) extends HP
case class Check(h: FOFormula) extends HP
case class Seq(p1: HP, p2: HP) extends HP
case class Choose(p1: HP, p2: HP) extends HP
case class Repeat(p1: HP, 
                  h: FOFormula,
                  inv_hints: List[FOFormula]) extends HP
case class Evolve(derivs: List[(String,Term)], 
                  h: FOFormula,
                  inv_hints: List[FOFormula],
                  sols: List[FOFormula]) extends HP


abstract class DLFormula
case class NoModality(fo: FOFormula) extends DLFormula
case class Box(hp: HP, rest: DLFormula) extends DLFormula
case class Diamond(hp: HP, rest: DLFormula) extends DLFormula


abstract class Goal
case class Sequent(ctxt: List[FOFormula], 
                   succedent: DLFormula) extends Goal
//case class FOGoal(fm: FOFormula) extends Goal




case class ProofRule( name: String,
                      premiseFV: List[String],
                      premises: List[Sequent],
                      conclusion: Sequent)


abstract class Result
case class Proved(rule: String) extends Result
case class Disproved() extends Result
case class GaveUp() extends Result


