package KeYmaeraD.Tests

import org.scalatest.FunSuite

import KeYmaeraD._
import KeYmaeraD.P._
import KeYmaeraD.Prover._

class UnitTests extends FunSuite {

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

    val fm2 = parseFormula("forall i : C . i = j()")

    assert (substitute_Formula("i", x, fm1) === fm1s)
    assert (substitute_Formula("i", x, fm2) === fm2)
  }

  test("substitution in formulas") {
    val x = Fn("x", Nil)
    val y = Fn("y", Nil)
    val fm1 = parseFormula("[g(i) := f(i)] true")
    val fm2 = parseFormula("[g(x()) := f(x())] true")
    assert (substitute_Formula("i", x, fm1) === fm2)

  }



}
