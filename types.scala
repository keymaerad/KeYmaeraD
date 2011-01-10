package DLBanyan

sealed abstract class Term
case class Var(s: String) extends Term
case class Fn(f: String, ps: List[Term]) extends Term
case class Num(n: Exact.Num) extends Term

abstract class Pred
case class R(r: String, ps: List[Term]) extends Pred


sealed abstract class Sort
case class St(nm: String) extends Sort
case object Real extends Sort

sealed abstract class Connective
case object And extends Connective
case object Or extends Connective
case object Imp extends Connective
case object Iff extends Connective

// first order formula
sealed abstract class Formula
case object True extends Formula
case object False extends Formula
case class Atom(p: Pred) extends Formula
case class Not(f: Formula) extends Formula
case class Binop(c: Connective, f1 : Formula, f2: Formula) extends Formula
case class Exists(v: String, f: Formula) extends Formula
case class Forall(v: String, f: Formula) extends Formula
case class ExistsOfSort(v: String, c: Sort, f: Formula) extends Formula
case class ForallOfSort(v: String, c: Sort, f: Formula) extends Formula
case class Box(hp: HP, rest: Formula) extends Formula
case class Diamond(hp: HP, rest: Formula) extends Formula

// formula with a hole in it.
sealed abstract class FormulaCtxt
case object Hole extends FormulaCtxt
case class NotCtxt(f: FormulaCtxt) extends FormulaCtxt
case class AndCtxt1(f1: FormulaCtxt, f2: Formula) extends FormulaCtxt
case class AndCtxt2(f1: Formula, f2: FormulaCtxt) extends FormulaCtxt
case class OrCtxt1(f1: FormulaCtxt, f2: Formula) extends FormulaCtxt
case class OrCtxt2(f1: Formula, f2: FormulaCtxt) extends FormulaCtxt
case class ImpCtxt1(f1: FormulaCtxt, f2: Formula) extends FormulaCtxt
case class ImpCtxt2(f1: Formula, f2: FormulaCtxt) extends FormulaCtxt
case class IffCtxt1(f1: FormulaCtxt, f2: Formula) extends FormulaCtxt
case class IffCtxt2(f1: Formula, f2: FormulaCtxt) extends FormulaCtxt
case class ExistsCtxt(v: String, f: FormulaCtxt) extends FormulaCtxt
case class ForallCtxt(v: String, f: FormulaCtxt) extends FormulaCtxt
case class ExistsOfSortCtxt(v: String, c: Sort, f: FormulaCtxt) 
     extends FormulaCtxt
case class ForallOfSortCtxt(v: String, c: Sort, f: FormulaCtxt) 
     extends FormulaCtxt
case class BoxCtxt(hp: HP, rest: FormulaCtxt) extends FormulaCtxt
case class DiamondCtxt(hp: HP, rest: FormulaCtxt) extends FormulaCtxt





sealed abstract class HP
case class Assign( vs : List[(Fn, Term)]) extends HP
case class AssignAny(v: Fn) extends HP
case class AssignQuantified(i : String, c: Sort, f : Fn, v: Term) extends HP
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


