dl('load, "examples/llcsimple.dl")
val rl = loopInduction(
  parseFormula(
    "(b()>0 & B() > 0 & B() > b() & ~(f() = l()) & eps() > 0) &" + 
    "(((b()*B()*x(l()) > b()*B()*x(f()) + " + 
    "(1/2) * (B()*v(f())^2 -  b()*v(l())^2) & " +
    "x(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 )    )   )"))


val everythingT: Tactic = 
  composeT(
    repeatT(
      eitherlistT(List(hpalphaT, 
                       alphaT, 
                       betaT, 
                       substT))),
    eitherT(nonarithcloseT, hidethencloseT))



val ch_brake = 
  composelistT(List(repeatT(hpalpha1T),
                    usehintsT(RightP(1)),
                    repeatT(hpalpha1T),
                    instantiate0T,
                    repeatT(substT),
                    hideunivsT,
                    repeatT(nullarizeT),
                    everythingT
                      ))


val ch_whatev = 
  composelistT(List(repeatT(eitherT(hpalphaT,alphaT)),
                    usehintsT(RightP(1)),
                    repeatT(hpalpha1T),
                    instantiate0T,
                    repeatT(substT),
                    hideunivsT,
                    repeatT(nullarizeT),
                    everythingT
                      ))

val indtct =                           
  composeT(
   repeatT(eitherT(hpalphaT,alphaT)),
   branchT(tryruleT(choose),
           List(ch_brake,ch_whatev)))

    



dl('gotoroot)
dl('tactic,  branchT(tryruleT(rl),
                     List(tryruleatT(close)(RightP(0)),
                          indtct,
                          repeatT(trylistofrulesT(List(close,andLeft)))
                          )))


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
