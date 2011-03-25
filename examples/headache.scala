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

val okcuttct = cutT(
  StandardCut,
  parseFormula(
   "(x(F)<x(L)&~F=L&(forall i:C.~i=F &~i=L==>x(i)<x(F)|x(L)<x(i)) )" + 
    "==>2*B()*x(L)>2*B()*x(F)+v(F)^2-v(L)^2"
  ),
  parseFormula(
   "(x(F)<x(L)&~F=L&(forall i:C.~i=F &~i=L==>x(i)<x(F)|x(L)<x(i)) )" 
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



val impsg1 = 
  composelistT(
    tryruleT(orLeft)*,
    tryruleT(andLeft)*
  )

val origok = 
  composelistT(
    tryruleT(andRight)*
  )


val orsg1tct = unitT 

val orsg2tct = 
 composelistT(
   tryruleT(andLeft)*,
   instantiate1T(St("C")),
   vacuousT*,
   branchT(tryruleT(impLeft),
           List(impsg1,origok))
 )


val sg1tct = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    branchT(tryruleT(orLeft),
            List(orsg1tct,orsg2tct))
             )


val uselemma =  branchT(tryruleT(impLeft),
                        List(sg1tct,
                             tryruleT(close)))

val provelemma = 
  composelistT()

val starttct = 
  composelistT(hpalpha1T*,
               diffsolveT(RightP(0),Endpoint),
               hpalpha1T*,
               instantiate3T,
               branchT(okcuttct,
                       List(provelemma,
                            uselemma))

             )



dl('gotoroot)
dl('tactic, starttct)


