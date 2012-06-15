package KeYmaeraD.Tests

import org.scalatest.FunSuite

import KeYmaeraD._
import KeYmaeraD.P._
import KeYmaeraD.Prover._

class UnitTests extends FunSuite {

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

  }



}
