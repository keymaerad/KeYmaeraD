dl('load, "examples/headache.dl")


val cuttct = cutT(
  DirectedCut,
  parseFormula(
    "b()*B()*X1>b()*B()*X2+1/2*(B()*V1^2-b()*V2^2)+" + 
     "B()*(A()+b())*(1/2*A()*eps()^2+eps()*V1)"
  ),
  parseFormula(
    "b()*B()*X1>b()*B()*X2+1/2*(B()*V1^2-b()*V2^2)+" + 
     "B()*(A()+b())*(1/2*A()*s()^2+s()*V1)"
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




val sg1tct = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    tryruleT(orLeft)*
                
             )



val starttct = 
  composelistT(hpalpha1T*,
               diffsolveT(RightP(0),Endpoint),
               hpalpha1T*,
               instantiate3T,
               branchT(tryruleT(impLeft),
                       List(sg1tct))
             )



dl('gotoroot)
dl('tactic, starttct)


