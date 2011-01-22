dl('load, "examples/llcsimple.dl")
val rl = loopInduction(
  parseFormula(
    "(b()>0 & B() > 0 & ~(f() = l()) & eps() >= 0) &" + 
    "(((b()*B()*x(l()) > b()*B()*x(f()) + " + 
    "(1/2) * (B()*v(f())^2 -  b()*v(l())^2) & " +
    "x(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 ) | x(l()) < x(f()) | l() = f()))"))

val qdsrT = 
  tryruleT(
    qDiffSolve(Endpoint)(List(
    parseFormula("forall s . x(s, i) = (1/2) *a(i) * s^2 + v(i) * s + x(i)"),
    parseFormula("forall s . v(s, i) = a(i) * s + v(i)"),
    parseFormula("forall s . t(s) = t()  + s")
    )))

val ch_brake = 
  composelistT(List(repeatT(hpalpha1T),
                    qdsrT,
                    repeatT(hpalpha1T),
                    instantiate0T,
                    repeatT(substT),
                    hideunivsT,
                    repeatT(nullarizeT),
                    alleasyT
                      ))


val ch_whatev = repeatT(eitherT(hpalphaT,alphaT))
val ch_stopped = repeatT(eitherT(hpalphaT,alphaT))

val indtct =                           
  composeT(
   repeatT(eitherT(hpalphaT,alphaT)),
   branchT(tryruleT(choose),
           List(branchT(tryruleT(choose), List(ch_brake,ch_whatev) ),
                ch_stopped )))
    



dl('gotoroot)
dl('tactic,  branchT(tryruleT(rl),
                     List(tryruleatT(close)(RightP(0)),
                          indtct,
                          repeatT(eitherT(trylistofrulesT(List(andLeft)), 
                                          tryruleatT(close)(RightP(0))))
                        )
                          ))

/*
dl('tactic, trylistofrulesT(List(rl)))
dl('tactic, applyToLeavesT(tryruleatT(close) (RightP(0))))
dl('tactic, applyToLeavesT(repeatT(alphaT)))
dl('tactic, applyToLeavesT(tryruleatT(close) (RightP(0))))
dl('tactic, applyToLeavesT(repeatT(eitherT(hpalphaT,alphaT))))
dl('tactic, applyToLeavesT(trylistofrulesT(List(
  qDiffSolve(Endpoint)(List(
    parseFormula("forall s . x(s, i) = (1/2) *a(i) * s^2 + v(i) * s + x(i)"),
    parseFormula("forall s . v(s, i) = a(i) * s + v(i)"),
    parseFormula("forall s . t(s) = t()  + s")
    ))))))
*/
