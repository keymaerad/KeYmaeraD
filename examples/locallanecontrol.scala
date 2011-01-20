dl('load, "examples/locallanecontrol.dl")
val rl = loopInduction(
  parseFormula(
    "(~(f() = l()) & eps() >= 0) &" + 
    "(((b()*B()*x(l()) > b()*B()*x(f()) + " + 
    "(1/2) * (B()*v(f())^2 -  b()*v(l())^2) & " +
    "v(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 ) | v(l()) < x(f()) | l() = f()))"))
dl('gotoroot)
dl('tactic, trylistofrulesT(List(rl)))
dl('tactic, applyToLeavesT(tryruleatT(close) (RightP(0))))
dl('tactic, applyToLeavesT(repeatT(alphaT)))
dl('tactic, applyToLeavesT(tryruleatT(close) (RightP(0))))
dl('tactic, applyToLeavesT(repeatT(eitherT(hpeasyT,alphaT))))
dl('tactic, applyToLeavesT(trylistofrulesT(List(
  qDiffSolve(Endpoint)(List(
    parseFormula("forall t . x(t, i) = (1/2) *a(i) * t^2 + v(i) * t + x(i)"),
    parseFormula("forall t . v(t, i) = a(i) * t + v(i)")
    ))))))