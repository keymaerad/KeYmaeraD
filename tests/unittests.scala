package KeYmaeraD.Tests

import org.scalatest.FunSuite

import KeYmaeraD._
import KeYmaeraD.P._
import KeYmaeraD.Prover._

class UnitTests extends FunSuite {

  test("uniqify") {
    val x0 = "x"
    val x1 = uniqify(x0)
    val x2 = uniqify(x1)

    assert (! (x0 == x1))
    assert (! (x1 == x2))

    assert (ununiqify(x0) === "x")
    assert (ununiqify(x1) === "x")
    assert (ununiqify(x2) === "x")

    assert (getuniqid(x1) > getuniqid(x0))
    assert (getuniqid(x2) > getuniqid(x1))
  }

  test("hasFn") {
   val fm1 = parseFormula("g(x()) = f(x())  + 16 * h(x())")
   assert(hasFn("x", fm1))
   assert(hasFn("f", fm1))
   assert(hasFn("g", fm1))
   assert(hasFn("h", fm1))
   assert(!hasFn("y", fm1))

   val fm2 = parseFormula("[w() := x()] true")
   assert(hasFn("x", fm2))

   val fm3 = parseFormula("[w() := x()][{w() := z() + 1}*] true")
   assert(hasFn("x", fm3))
   assert(hasFn("z", fm3))
   assert(!hasFn("y", fm3))

  }

  test("alpha equality") {
    assert (alphaeq(True, True))
    assert (alphaeq(False, False))
    assert (!alphaeq(False, True))

    val fm0 = parseFormula("x() = 0")
    val fm1 = parseFormula("x() = 0")
    assert (alphaeq(fm0, fm1))

    val fm2 = parseFormula("y() = 0")
    assert (!alphaeq(fm1, fm2))

    val fm3 = parseFormula("x() = 1 | y() = 1")
    val fm4 = parseFormula("x() = 1 & y() = 1")

    assert (alphaeq(Not(fm3), Not(fm3)))
    assert (!alphaeq(fm3, fm4))

    val fm5 = parseFormula("forall i : C . x(i) = 0")
    val fm6 = parseFormula("exists i : C . x(i) = 0")

    assert (!alphaeq(fm5, fm6))

    val fm7 = parseFormula("forall ii : C . x(ii) = 0")

    assert (alphaeq(fm5, fm7))

    val fm8 = parseFormula("[x() := 4] x() = 4")
    val fm9 = parseFormula("<x() := 4> x() = 4")

    assert (!alphaeq(fm8, fm9))

    val fm10 = parseFormula("[(?forall i. y(i) = 0) ] x() = 4")
    val fm11 = parseFormula("[(?forall ii. y(ii) = 0) ] x() = 4")

    assert (alphaeq(fm10, fm11))

    val fm12 =
      parseFormula("[forall i : C {x(i)' = 4, y(i)' = 2 * y(i); true } ] x(j()) = 4")
    val fm13 =
      parseFormula("[forall ii : C {x(ii)' = 4, y(ii)' = 2 * y(ii); true } ] x(j()) = 4")

    assert (alphaeq(fm12, fm13))

    val fm14 = parseFormula("[x() := 0] x() = 0")
    val fm15 = parseFormula("[y() := 0] y() = 0")

    assert (!alphaeq(fm14, fm15))

    val fm16 = parseFormula("[x() := 0 ; ((?true) ++ y() := 0)] x() = 0")
    val fm17 = parseFormula("[x() := 0 ; ((?true) ++ x() := 0)] x() = 0")

    assert (alphaeq(fm16, fm16))
    assert (!alphaeq(fm16, fm17))

  }

  test("substitution in terms") {
    val x = Fn("x", Nil)
    val y = Fn("y", Nil)
    val v = Var("v")
    assert (substitute_Term("v", x, v) === x)

    val tm1 = Fn("f", List(v, v))
    val tm2 = Fn("f", List(x, x))

    assert (substitute_Term("v", x, tm1) === tm2)

  }

  test("capture-avoiding substitution") {
    val x = Fn("x", List(Var("i")))

    val fm1 = parseFormula("forall k : C . i = k")
    val fm1s = parseFormula("forall k : C . x(i) = k")

    assert (substitute_Formula("i", x, fm1) === fm1s)

    val fm2 = parseFormula("forall i : C . i = j()")

    assert (substitute_Formula("i", x, fm2) === fm2)

    val fm3 = parseFormula("forall i : C . i = k")
    val fm4 = parseFormula("forall ii : C . ii = x(i)")

    assert (alphaeq(substitute_Formula("k", x, fm3), fm4))

  }

  test("substitution in formulas") {
    val x = Fn("x", Nil)
    val y = Fn("y", Nil)
    val fm1 = parseFormula("[g(i) := f(i)] true")
    val fm2 = parseFormula("[g(x()) := f(x())] true")
    assert (substitute_Formula("i", x, fm1) === fm2)

    val fm3 = parseFormula("X > 4 & X < 10")
    val fm4 = parseFormula("x() > 4 & x() < 10")
    assert (substitute_Formula("X", x, fm3) === fm4)

  }

 test("equality substitution") {
   val x = Fn("x", Nil)
   val y = Fn("y", Nil)
   val fm1 = parseFormula("g(x()) = f(x())  + 16 * h(x())")
   val fm2 = parseFormula("g(y()) = f(y())  + 16 * h(y())")
   assert(try_equality_substitution(x, y, fm1) == Some(fm2))

   val fm3 = parseFormula("[w() := x()][{w() := w() + 1}*] true")
   val fm4 = parseFormula("[w() := y()][{w() := w() + 1}*] true")
   assert(try_equality_substitution(x, y, fm3) == Some(fm4))

   // We only substitute in modalities if we can guarantee
   // that we've gotten rid of all instances.
   val fm5 = parseFormula("[w() := x()][{w() := x() + 1}*] true")
   // Substituting should give [w() := y()][{w() := y() + 1}*] true,
   // but we have not implemented the analysis that would allow this.
   // Instead of only eliminating the outside instance of x, we fail.
   assert(try_equality_substitution(x, y, fm5) == None)


   val fm6 = parseFormula("[w() := y()][{w() := w() + 1}*] true")
   assert(try_equality_substitution(x, y, fm6) == Some(fm6))
 }

 test("extraction") {

   val tm1 = Fn("x", Nil)

   val fm1 = parseFormula("y() = 0 & x() = 1")

   assert (extract(tm1, fm1)(tm1) === fm1)

   val tm2 = Var("i")
   val fm2 = parseFormula("forall i : C. i = j()")

   assert (extract(tm2, fm2)(tm2) === fm2)

   val tm3 = Fn("k", Nil)
   val fm3 = parseFormula("forall i : C. k() = j()")

   assert (extract(tm2, fm2)(tm3) === fm3)

 }

 test("unification") {
   val x = Fn("x", Nil)
   val y = Fn("y", Nil)
   val fm1 = parseFormula("y() = 0 & x() = 1")
   assert (unify(fm1, fm1) === Some(nilmap))

   val fm2 = parseFormula("Y = 0 & X = 1")

   unify(fm1, fm2) match {
     case None => assert (false)
     case Some(subs) =>
       assert (subs("X") === x)
       assert (subs("Y") === y)
   }

 }


}
