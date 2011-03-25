dl('load, "examples/tylenol.dl")


val cuttct0 = cutT(
  StandardCut,
  parseFormula(
    "2*B()*X1>2*B()*X2+ V2^2 - V1^2 +" + 
     "(A()+B())*(A()*eps()^2+2 * eps()*V2)"
  ),
  parseFormula(
     "(A()+B())*(A()*eps()^2+2 * eps()*V2) >= "+
     "(A()+B())*(A()*s()^2+2 * s()*V2) "
  )
)


val cuttct = cutT(
  DirectedCut,
  parseFormula(
    "2*B()*X1>2*B()*X2+ V2^2 - V1^2 +" + 
     "(A()+B())*(A()*eps()^2+2 * eps()*V2)"
  ),
  parseFormula(
    "2*B()*X1>2*B()*X2+ V2^2 - V1^2 +" + 
     "(A()+B())*(A()*s()^2+2 * s()*V2)"
  )
)


val okcuttct = cutT(
  StandardCut,
  parseFormula(
   "(x(F)<x(L)&~F=L )" + 
    "==>2*B()*x(L)>2*B()*x(F)+v(F)^2-v(L)^2"
  ),
  parseFormula(
   "x(F)<x(L)&~F=L" 
  )
)


val safetyfm=
  parseFormula(
    "(forall l:C . x(F)<x(l)&~F=l&(forall i:C.~i=F&~i=l==>x(i)<x(F)"+
    "|x(l)<x(i))==>2*B()*x(l)>2*B()*x(F)+v(F)^2-v(l)^2+(A()+B())*(A()*eps()^2+2*eps()*v(F)))"
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



val provecut =
 composelistT(
   tryrulepredT(hide) (fm => fm match {case Binop(Or,_,_) => true case _ => false}),
   tryruleT(not),
   nullarizeT*,
   tryruleunifyT(hide) (
     parseFormula( "X1=1/2*A*s()^2+V*s()+X2")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "V1=A*s()+V")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "2*B()*X2>2*B()*X1 + V1^2-V2^2")
   )*,
   substT*,
   hidethencloseT
 )

val hardcase = 
  composelistT(
    nullarizeT*,
    substT*,
    hidethencloseT
  )


val impsg1 = 
  composelistT(
    tryruleT(andLeft)*,
    hideunivsT(St("C")),
    branchT(cuttct,
            List(provecut, 
                 branchT(tryruleT(orLeft),
                         List(branchT(tryruleT(orLeft),
                                      List(hardcase, 
                                           composelistT(nullarizeT*,hidethencloseT))),
                              composelistT(
                                tryruleT(andLeft)*,
                                hideunivsT(St("C")),
                                nullarizeT*,
                                substT*,
                                hidethencloseT
                              )
                            )
                       )
               )
          )
  )


val orsgtct0 = unitT

val orsg1tct = 
  branchT(tryruleT(orLeft), List(orsgtct0))

val orsg2tct = 
 composelistT(
   tryruleunifyT(andLeft)(Binop(And, safetyfm, Atom(R("=",List(Var("YY"),Var("ZZ")))))),
   instantiate1T(St("C")),
   vacuousT*,
   branchT(tryruleT(impLeft),
           List(impsg1,tryruleT(close)))
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

val andbranch1 = 
  composelistT(
    hidedoublequantT
  )

val provelemma = 
  branchT(tryruleT(andRight),
          List(branchT(tryruleT(andRight),
                       List(andbranch1, composelistT(tryruleT(not), substT*) )),
             unitT)
          )


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


