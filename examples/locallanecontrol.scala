dl('load, "examples/locallanecontrol.dl")
val rl = loopInduction(
  parseFormula(
    "(~(f() = l()) & eps() >= 0) &" + 
    "((b()*B()*x(l()) > b()*B()*x(f()) + " + 
    "(1/2) * (B()*v(f())^2 -  b()*v(l())^2) & " +
    "v(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 ) | v(l()) < x(f()) | l() = f())"))
dl('gotoroot)
dl('tactic, trylistofrulesT(List(rl)))
dl('tactic, applyToLeavesT(tryruleatT(close) (RightP(0))))
