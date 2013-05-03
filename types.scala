package KeYmaeraD

sealed abstract class Term
case class Var(s: String) extends Term
case class Fn(f: String, ps: List[Term]) extends Term
case class Num(n: Exact.Num) extends Term

sealed abstract class Pred
case class R(r: String, ps: List[Term]) extends Pred


sealed abstract class Sort
case class St(nm: String) extends Sort
case object Real extends Sort
case object AnySort extends Sort

sealed abstract class Connective
case object And extends Connective
case object Or extends Connective
case object Imp extends Connective
case object Iff extends Connective

sealed abstract class QuantifierType
case object Forall extends QuantifierType
case object Exists extends QuantifierType


sealed abstract class ModalityType
case object Box extends ModalityType
case object Diamond extends ModalityType

// first order formula
sealed abstract class Formula
case object True extends Formula
case object False extends Formula
case class Atom(p : Pred) extends Formula
case class Not(f : Formula) extends Formula
case class Binop(c : Connective, f1 : Formula, f2 : Formula) extends Formula
case class Quantifier(t : QuantifierType, v : String,
                      c: Sort, f: Formula) extends Formula
case class Modality(m : ModalityType, hp: HP, rest : Formula) extends Formula


sealed abstract class HP
case class Assign(vs : List[(Fn, Term)]) extends HP
case class AssignAny(v: Fn) extends HP
case class AssignAnyQuantified(i: String, c: Sort, v: Fn) extends HP
case class AssignQuantified(i : String,
                            c: Sort,
                            vs: List[(Fn,Term)]) extends HP
case class Check(h: Formula) extends HP
case class Seq(p1: HP, p2: HP) extends HP
case class Choose(p1: HP, p2: HP) extends HP
case class Loop(p1: HP,
                h: Formula,
                inv_hints: List[Formula]) extends HP
case class Evolve(derivs: List[(Fn,Term)],
                  h: Formula,
                  inv_hints: List[Formula],
                  sols: List[Formula]) extends HP
case class EvolveQuantified(i:String,
                            c: Sort,
                            vs : List[(Fn, Term)],
                            h : Formula,
                            sols: List[Formula]
                            ) extends HP


//abstract class Goal
case class Sequent(fn_sorts: Map[String, (List[Sort], Sort)],
                   ctxt: List[Formula],
                   scdts: List[Formula])
//case class FOGoal(fm: Formula) extends Goal

class Lock() extends Object()

class Unimplemented() extends Exception()

