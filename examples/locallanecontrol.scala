dl('load, "examples/locallanecontrol.dl")
val rl = loopInduction(
  parseFormula(
    "((x(l()) > x(f()) + (1/2) * (v(f())^2 -  v(l())^2) & " +
    "v(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 ) | v(l()) < x(f()) | l() = f())"))
dl('gotoroot)
dl('tactic, trylistofrulesT(List(rl)))
