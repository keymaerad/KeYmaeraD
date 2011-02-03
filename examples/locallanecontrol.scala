dl('load, "examples/locallanecontrol.dl")
val rl = loopInduction(
  parseFormula(
    "(b()>0 & B() > 0 & ~(f() = l()) & eps() >= 0) &" + 
    "(((b()*B()*x(l()) > b()*B()*x(f()) + " + 
    "(1/2) * (B()*v(f())^2 -  b()*v(l())^2) & " +
    "x(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 ) | x(l()) < x(f()) | l() = f()))"))



val mostthingsT = 
    repeatT(
      eitherlistT(hpalphaT, 
                  alphaT, 
                  nonarithcloseT,
                  betaT, 
                  substT))


val everythingT: Tactic = 
  composeT(
    repeatT(
      eitherlistT(hpalphaT, 
                  alphaT, 
                  nonarithcloseT,
                  betaT, 
                  substT)),
    eitherT(nonarithcloseT, hidethencloseT))





val ch_brake = 
  composelistT(repeatT(hpalpha1T),
               diffsolveT(RightP(1),Endpoint),
               repeatT(hpalpha1T),
               instantiate0T(St("C")),
               repeatT(substT),
               hideunivsT(St("C")),
               repeatT(nullarizeT),
               repeatT(vacuousT),
               everythingT
                      )


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


