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


sealed abstract class TermValue
case class RealV(v : Double)  extends TermValue
case class ObjectV(s : Sort,  id : Int) extends TermValue

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



 class State()  {

   import scala.collection.mutable.HashMap

   var sizes : Map[String, Int] = null

   // map a symbol to its signature
   // and its starting index in the appropriate state array
   var sig : HashMap[String, (List[Sort], Sort, Int)] = null

   // Initialize the state vectors.
   var signals : Array[Double] = null
   var objects : Array[Int] = null


   def this(sig1 : Map[String, (List[Sort], Sort)],
             // the cardinalities of the named sorts
             sizes1 : Map[String, Int]) = {
    this()
    sizes = sizes1    
    sig =   new HashMap[String, (List[Sort], Sort, Int)]()

    var sptr = 0
    var optr = 0
    for ((x, (args, res)) <- sig1) (args, res) match {
      case (Nil, Real) => sig.put(x, (args, res, sptr))
        sptr +=1
      case (List(St(c)), Real) => sig.put(x, (args, res, sptr))
        sptr += sizes(c)
      case (Nil, St(c)) => sig.put(x, (args, res, optr))
        optr +=1
      case (List(St(c1)), St(c2)) => sig.put(x, (args, res, optr))
        optr += sizes(c1)
      case _ => throw new Error("cannot deal")
     }   

    signals = new Array[Double](sptr)
    objects = new Array[Int](optr)

  }

  def this(that : State) = {
    this()
    sizes = that.sizes
    sig = that.sig
    signals = that.signals.clone()
    objects = that.objects.clone()
  }


 }

 type IHMap[A, B] = scala.collection.immutable.HashMap[A, B]

 private val empty = new IHMap[String, TermValue]()

 def evalTerm(st : State,
              env : IHMap[String, TermValue])
              (tm : Term ) : TermValue = tm match {
   case Var(x) => env(x)

   case Fn("+", args) =>
     args.map(evalTerm(st, env)) match {
       case List(RealV(x), RealV(y)) => RealV(x + y)
       case _ => throw new Error("evalTerm")
     }

   case Fn("-", args) =>
     args.map(evalTerm(st, env)) match {
       case List(RealV(x), RealV(y)) => RealV(x - y)
       case List(RealV(x)) => RealV(-x)
       case _ => throw new Error("evalTerm")
     }

   case Fn("*", args) =>
     args.map(evalTerm(st, env)) match {
       case List(RealV(x), RealV(y)) => RealV(x * y)
       case _ => throw new Error("evalTerm")
     }

   case Fn("/", args) =>
     args.map(evalTerm(st, env)) match {
       case List(RealV(x), RealV(y)) => RealV(x / y)
       case _ => throw new Error("evalTerm")
     }

   case Fn("^", args) =>
     args.map(evalTerm(st, env)) match {
       case List(RealV(x), RealV(y)) => RealV(scala.math.pow(x, y))
       case _ => throw new Error("evalTerm")
     }

   case Fn(f, args) => (st.sig(f), args.map(evalTerm(st, env))) match {
      case ((Nil, Real, idx), Nil) => RealV(st.signals(idx))
      case ((List(St(c)), Real, idx), List(ObjectV(St(c1), n))) => 
        assert (c == c1)
        RealV(st.signals(idx + n.intValue))
      case ((Nil, St(c), idx), Nil) => ObjectV(St(c), st.objects(idx))
      case ((List(St(c1)), St(c2), idx), List(ObjectV(St(c3), n)) ) =>
        assert (c1 == c3)
        ObjectV(St(c2), st.objects(idx + n.intValue))
     case _ => throw new Error("evalTerm")
   }

   case Num(n) => RealV(numToDouble(n))

 }

 def evalFormula (st : State,
                  env : IHMap[String, TermValue])
                 (fm : Formula) : Boolean = fm match {
   case True => true
   case False => false
   case Atom(R(r, tms)) => (r, tms.map(evalTerm(st, env))) match {
     case ("=", List(RealV(x), RealV(y))) => x == y
     case ("=", List(ObjectV(c1, x1), ObjectV(c2, x2))) if c1 == c2 => !(x1 == x2)
     case ("/=", List(RealV(x), RealV(y))) => !(x == y)
     case ("/=", List(ObjectV(c1, x1), ObjectV(c2, x2))) if c1 == c2 => !(x1 == x2)
     case ("<", List(RealV(x), RealV(y))) => x < y
     case ("<=", List(RealV(x), RealV(y))) => x <= y
     case (">=", List(RealV(x), RealV(y))) => x >= y
     case (">", List(RealV(x), RealV(y))) => x > y
     case _ => throw new Error("evalFormula")
   }
     
   case Not(fm1) => (!evalFormula(st, env)(fm1))
   case Binop(And, f1, f2) =>
     evalFormula(st, env)(f1) && evalFormula(st, env)(f2)
   case Binop(Or, f1, f2) =>
     evalFormula(st, env)(f1) || evalFormula(st, env)(f2)
   case Binop(Imp, f1, f2) =>
     (!evalFormula(st, env)(f1)) || evalFormula(st, env)(f2)
   case Binop(Iff, f1, f2) =>
     val (v1, v2) = (evalFormula(st, env)(f1), evalFormula(st, env)(f2))
       ( ( (!v1) || v2) & ( (!v2) || v1))
   case Quantifier(Forall, St(c), i, fm1) =>
     for (k <- Range(0, st.sizes(c))) {
       if (!evalFormula(st, env + ((i, ObjectV(St(c), k))))(fm1)) {
         return false
       }

     }
     true
   case _ => throw new Error("evalFormula")
   
 }


  val rng = new scala.util.Random()

  // Run a hybrid program.
  // we need:
  // a map from named sorts to natural numbers, indicating the cardinalities
  // a starting state
  // a step size
  // a stack size --- the number of past states to remember so they can be resumed if we hit a failing check.
  //  if BACKTRACKABLE is set to true, we don't do any copying of state 

 def updateState (st : State,
                  ty : (List[Sort], Sort, Int),
                  args : List[TermValue],
                  v : TermValue) : Unit = 
    (ty, args, v) match {
         case ((Nil, Real, idx), Nil, RealV(x) ) =>
           st.signals.update(idx, x)
         case ((List(St(c)), Real, idx), List(ObjectV(St(c1), ob)), RealV(x)) =>
           assert (c == c1)
           st.signals.update(idx + ob, x)
         case ((Nil, St(c), idx), Nil, ObjectV(St(c1), ob)) =>
           assert (c == c1)
           st.objects.update(idx, ob)
         case ((List(St(d)), St(c), idx), List(ObjectV(St(d1), ob1)), ObjectV(St(c1), ob)) =>
           assert (c == c1)
           st.objects.update(idx + ob1, ob)
         case _ => throw new Error("updateState")
    }

 def doTransition(st : State, tr : Transition) : Unit = tr match {

   case AssignTransition(vs) =>
     // copy the old state
     val stOld = new State(st)
     vs.map( {case (Fn(f, args), t) =>
       updateState(st, stOld.sig(f), args.map(evalTerm(stOld, empty)), evalTerm(stOld, empty)(t))
            })
     ()

   case AssignAnyTransition(f : Fn) => f match {
     case Fn(g, args) => st.sig(g) match {
       case(params, St(c), idx) =>
         updateState(st, (params, St(c), idx),
                     args.map(evalTerm(st, empty)),
                     ObjectV(St(c), rng.nextInt(st.sizes(g))))
       case(params, Real, idx) =>
         updateState(st, (params, Real, idx),
                     args.map(evalTerm(st, empty)),
                     RealV(rng.nextDouble())) // between 0.0 and 1.0
       case _ => throw new Error("doTransition")
     }
   }

   case AssignQuantifiedTransition(i, c, vs) => throw new Error("doTransition: unimplemented")

   case _ => throw new Error("doTransition")
     

 }


  // a state is a double[] and an int[]

}
