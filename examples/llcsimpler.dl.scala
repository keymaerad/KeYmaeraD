object Script {

val rl = loopInduction(
  parseFormula(
    "(A() > 0 & B() > 0 & ~(f() = l()) & eps() > 0) &" + 
    "(((B()*x(l()) > B()*x(f()) + " + 
    "(1/2) * (v(f())^2 -  v(l())^2) & " +
    "x(l()) > x(f()) &" +
    "v(f()) >= 0 &" +
    "v(l()) >= 0 )    )   )"))


val cuttct = cutT(
  DirectedCut,
  parseFormula(
    "B()*X1>B()*X2+1/2*(V1^2-V2^2)+" + 
     "(A()+B())*(1/2*A()*eps()^2+eps()*V1)"
  ),
  parseFormula(
    "B()*X1>B()*X2+1/2*(V1^2-V2^2)+" + 
     "(A()+B())*(1/2*A()*s()^2+s()*V1)"
  )
)

  
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
  composelistT(repeatT(hpalphaT),
               diffsolveT(RightP(1),Endpoint),
               repeatT(hpalphaT),
               instantiate0T(St("C")),
               repeatT(substT),
               hideunivsT(St("C")),
               repeatT(nullarizeT),
               repeatT(vacuousT),
               everythingT
             )

val whatev_finish = composelistT(
        repeatT(nullarizeT),
        repeatT(substT),
        branchT(cuttct,
                List(everythingT,
                     everythingT))

    )


val ch_whatev = 
  composelistT(repeatT(hpalphaT),
               diffsolveT(RightP(1),Endpoint),
               repeatT(hpalphaT),
               instantiate0T(St("C")),
               repeatT(substT),
               hideunivsT(St("C")),
               repeatT(hpalphaT),
               repeatT(vacuousT),
               branchT(tryruleT(impLeft),
                       List(branchT(tryruleT(impLeft),
                                    List(whatev_finish,
                                         composelistT(
                                           tryruleT(not),
                                           alleasyT))
                                  ),
                            composelistT(
                              tryruleT(not),
                              tryruleT(close))))
                  )



val indtct =                           
  composeT(
   repeatT(eitherT(hpalphaT,alphaT)),
   branchT(tryruleT(andRight),
           List(ch_brake,ch_whatev)))


val main =   branchT(tryruleT(rl),
                     List(tryruleatT(close)(RightP(0)),
                          indtct,
                          repeatT(trylistofrulesT(List(close,andLeft)))
                          ))  

}

