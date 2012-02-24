package KeYmaeraD.Simulation

import KeYmaeraD._


// question: how will the user be able to control the nondeterminism?
//

sealed abstract class Transition
case class AssignTransition(vs : List[(Fn, Term)]) extends Transition
case class AssignAnyTransition(f : Fn) extends Transition
case class AssignQuantifiedTransition(i : String,
                                      c : Sort,
                                      vs : List[(Fn, Term)]) extends Transition
case class AssignAnyQuantifiedTransition(i : String,
                                         c : Sort,
                                         v : Fn) extends Transition
case class CheckTransition(fm : Formula) extends Transition
case class EvolveTransition(derivs: List[(Fn,Term)], h : Formula) extends Transition
case class EvolveQuantifiedTransition(i : String,
                                      c : Sort,
                                      derivs: List[(Fn,Term)],
                                      h : Formula) extends Transition


sealed abstract class StateNode

class StateNodeRef(s1 : StateNode) {
  var s : StateNode = s1
  def set(s2 : StateNode) : Unit = {s = s2}
  def get() : StateNode = s
}

case class Terminal() extends StateNode
case class Split(s1 : StateNodeRef, s2 : StateNodeRef) extends StateNode
case class Step(t : Transition, s: StateNodeRef) extends StateNode

object Sim {

  // Compile a hybrid program into a finite automaton.

 private def compileHP_aux (hp : HP, next : StateNode) : StateNode = hp match {
   case Assign(vs) => Step(AssignTransition(vs), new StateNodeRef(next))
   case AssignAny(f) => Step(AssignAnyTransition(f), new StateNodeRef(next))
   case AssignQuantified(i, c, vs) => Step(AssignQuantifiedTransition(i, c, vs), new StateNodeRef(next))
   case AssignAnyQuantified(i, c, v) => Step(AssignAnyQuantifiedTransition(i, c, v), new StateNodeRef(next))
   case Check(h) => Step(CheckTransition(h), new StateNodeRef(next))


   case Seq(hp1, hp2) => compileHP_aux(hp1, compileHP_aux(hp2, next))
   case Choose(hp1, hp2) => Split(new StateNodeRef(compileHP_aux(hp1, next)),
                                  new StateNodeRef(compileHP_aux(hp2, next)))
   case Loop(hp, True, _) =>
     val r1 = new StateNodeRef(next);
     val sn = Split(r1,
                    new StateNodeRef(next));
     r1.set(sn)
     sn
          

//      .-----------------.
//      |                 |
//      V                 |
//  --?inv--> loop body --*---->
            
   case Loop(hp1, inv, _) =>
     val r1 = new StateNodeRef(next);
     val spl = Split(r1,
                     new StateNodeRef(next));
     val b = compileHP_aux(hp1, spl)
     val check = Step(CheckTransition(inv), new StateNodeRef(b))
     r1.set(check)
     check


// TODO: make these loops, too.

   case Evolve(derivs, h, _, _) => Step(EvolveTransition(derivs, h), new StateNodeRef(next))

   case EvolveQuantified(i, c, derivs, h, _) =>
                    Step(EvolveQuantifiedTransition(i, c, derivs, h), new StateNodeRef(next))

 }


 def compileHP (hp : HP) : StateNode = {
   compileHP_aux(hp, Terminal())
 }


 // evaluate a term to a double.

 def numToDouble(n : Exact.Num) : Double = n match {
   case Exact.Rational(p, q) => p.doubleValue / q.doubleValue
   case Exact.Integer(n) => n.doubleValue
 }


 class State(sig1 : Map[String, (List[Sort], Sort)],
             // the cardinalities of the named sorts
             sizes : Map[String, Int])  {

   import scala.collection.immutable.HashMap

   // map a symbol to its signature
   // and its address in the appropriate state array
   val sig : Map[String, (List[Sort], Sort, Int)] = new HashMap[String, (List[Sort], Sort, Int)]()

   val signals : Array[Double] = null
   val objects : Array[Int] = null 
   
 }

/*
 def evalTerm(sv : Array[Double],
              mp : Map[String, Int],
              tm : Term ) : Double = tm match {
   case Var(_) => throw new Error("cannot evaluate term with a free variable")

   case Fn(f, Nil) => mp.get(f) match {
     case Some(i) => sv(i)
     case None => throw new Error("could not find symbol: " + f)
   }

   case Fn(f, List(arg)) => mp.get(f) match {
     case Some(i) => sv(i)
     case None => throw new Error("could not find symbol: " + f)
   }

   case Num(n) => numToDouble(n)

 }

*/

  // Run a hybrid program.
  // we need:
  // a map from named sorts to natural numbers, indicating the cardinalities
  // a starting state
  // a step size
  // a stack size --- the number of past states to remember so they can be resumed if we hit a failing check.
  //  if BACKTRACKABLE is set to true, we don't do any copying of state 


  // a state is a double[] and an int[]

}
