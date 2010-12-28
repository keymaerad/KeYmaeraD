package DLBanyan

sealed abstract class Term
case class Var(s: String) extends Term
case class Fn(f: String, ps: List[Term]) extends Term
case class Num(n: Exact.Num) extends Term

abstract class Pred
case class R(r: String, ps: List[Term]) extends Pred


sealed abstract class Type
case class typ(nm: String) extends Type

// first order formula
sealed abstract class Formula
case object True extends Formula
case object False extends Formula
case class Atom(p: Pred) extends Formula
case class Not(f: Formula) extends Formula
case class And(f1: Formula, f2: Formula) extends Formula
case class Or(f1: Formula, f2: Formula) extends Formula
case class Imp(f1: Formula, f2: Formula) extends Formula
case class Iff(f1: Formula, f2: Formula) extends Formula
case class Exists(v: String, f: Formula) extends Formula
case class Forall(v: String, f: Formula) extends Formula
case class Box(hp: HP, rest: Formula) extends Formula
case class Diamond(hp: HP, rest: Formula) extends Formula
case class SchemaVar(v: String) extends Formula


sealed abstract class HP
case class Assign(s: String, v: Term) extends HP
case class AssignAny(s: String) extends HP
case class AssignQuantified(i : String, c: Type, f : Fn, v: Term) extends HP
case class Check(h: Formula) extends HP
case class Seq(p1: HP, p2: HP) extends HP
case class Choose(p1: HP, p2: HP) extends HP
case class Loop(p1: HP, 
                h: Formula,
                inv_hints: List[Formula]) extends HP
case class Evolve(derivs: List[(String,Term)], 
                  h: Formula,
                  inv_hints: List[Formula],
                  sols: List[Formula]) extends HP
case class EvolveQuantified(i:String, 
                            c: Type,
                            f : Fn, 
                            v : Term,
                            h : Formula
                            ) extends HP



//abstract class Goal
@serializable
case class Sequent(ctxt: List[Formula],
                   scdts: List[Formula]) // extends Goal
//case class FOGoal(fm: Formula) extends Goal

class Lock() extends Object()

class Unimplemented() extends Exception()

/*
case class ProofRule( name: String,
                      premiseFV: List[String],
                      premises: List[Sequent],
                      conclusion: Sequent)


*/


