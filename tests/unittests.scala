package KeYmaeraD.Tests

import org.scalatest.FunSuite

import KeYmaeraD._
import KeYmaeraD.P._
import KeYmaeraD.Prover._


class UnitTests extends FunSuite {

  test("substitution") {
    val x = Fn("x", Nil)
    val y = Fn("y", Nil)
    val v = Var("v")
    assert(substitute_Term("v", x, v) === x)

    val fm1 = parseFormula("[g(i) := f(i)] true")
    val fm2 = parseFormula("[g(x()) := f(x())] true")
    assert(substitute_Formula("i", x, fm1) === fm2)
  }



}
