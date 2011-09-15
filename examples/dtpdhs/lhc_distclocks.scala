dl('load, "examples/dtpdhs/lhc_distclocks.dl")

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


val okcuttctfm1 = 
  parseFormula(
   "2 * B() * X2 > 2 * B() * X1 + V1^2- V2^2 + (A+B())*(A *" +
   "(eps()-T3)^2+2*(eps()-T3)*V1)"
  )

val okcuttctfm2 = 
  parseFormula(
   "2 * B() * X2 > 2 * B() * X1 + V1^2- V2^2 + (A+B())*(A *" +
   "(s())^2+2*(s())*V1)"
  )

val okcuttct = cutT(
  DirectedCut,
  okcuttctfm1,
  okcuttctfm2
)

val okcuttct2fm1 =   parseFormula(
   "2 * B() * X2 > 2 * B() * X1 + V1^2- V2^2 + (A+B())*(A *" +
   "(eps()-T3)^2+2*(eps()-T3)*V1)"
  )

val okcuttct2fm2 =
  parseFormula(
   " (A+B())*(A *(s())^2+2*(s())*V1)  <= (A+B())*(A *(eps() - T3)^2+2*(eps() - T3)*V1) "
  )

val okcuttct2 = cutT(
  StandardCut,
  okcuttct2fm1,
  okcuttct2fm2
)



val hideforprovecut = 
  composelistT(
   tryruleunifyT(hide) (
     parseFormula( "B * s()  + V >=0")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "2*B()*X2>2*B()*X1 + V1^2-V2^2")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "1/2 * B  * s()^2  + V * s()  + X <= 1/2 * A() * s()^2  + V1 * s() + X1")
   )*
  )


val provecut = 
 composelistT(
   tryrulepredT(hide) (fm => fm match {case Binop(Or,_,_) => true case _ => false}),
   tryrulepredT(hide) (fm => fm match {case Binop(Imp,_,_) => true case _ => false}),
   alphaT*,
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
    cuttct<(
      provecut, 
      tryruleT(orLeft)<(
        tryruleT(orLeft)<(
          hardcase, 
          composelistT(nullarizeT*,hidethencloseT)),
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



val orsg2tct = 
 composelistT(
   tryruleT(andLeft)*,
   instantiate1T(St("C")),
   vacuousT*,
   impleftknownT*,
   tryruleT(impLeft)<(
     impsg1,
     tryruleT(andRight)<( 
       tryruleT(andRight) & nonarithcloseT, 
       composelistT(alphaT*, tryruleT(close))))
 )


val easy0 = 
  composelistT(
    nullarizeT*,
    substT*,
    hidethencloseT
)

val easy1 = easy0

val easy2 = 
  composelistT(
    alphaT*,
    hideunivsT(St("C")),
    easy0
  )

val easycase = 
  composelistT(
    alphaT*,
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(easy0, easy1),
      easy2)
  )



val sg1tct = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    alphaT*,
    impleftknownT*,
    nullarizeT*,
    substT*,
    okcuttct
  )


val uselemma =  sg1tct

val precond = 
    tryruleT(andRight)<(
      composelistT(
        tryrulepredT(hide)(fm => fm match { case Atom(R("<=",_)) => false case _ => true}),
        hidethencloseT
      ),
      composelistT(alphaT*,
                   tryruleT(commuteEquals),
                   tryruleT(close)
                 )
    )


val oror0tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    tryruleT(impLeft)<(hidethencloseT,precond)
  )

val oror1tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    hidethencloseT
  )

val oror2tct = 
  composelistT(
    alphaT*,
    instantiate1T(St("C")),
    vacuousT*,
    nullarizeT*,
    substT*,
    tryruleT(impLeft)<(
      tryruleT(impLeft)<(
        cuttct<(
          hideforprovecut & hidethencloseT, 
          hidethencloseT),
        precond
      ),
      precond
    )
    
  )


val or0tct = 
  composelistT(
    alphaT*,
    hideunivsT(St("C")),
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(oror0tct,oror1tct), 
      oror2tct)
  )



val andbranch1 = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    alphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight) & tryruleT(close),
      composelistT(
        composelistT(
          impleftknownT*
        ),
        tryruleT(orLeft)<(
          tryruleT(orLeft)<(or0tct,or0tct),
          or0tct)

      )
    )
  )


val diffinv = parseFormula(
  "forall f : C. forall l : C. " +
   "(e(f) = 1 & e(l) = 1 & id(f) <= id(l))  ==> " +
"  ( (v(f) + a(f) * (eps() - t(f)) >= 0 & " +
"2 * B() *  x(l)  > 2 *  B() * x(f) + v(f)^2 - v(l)^2 " +
     " + (a(f) + B()) * (a(f) * (eps() - t(f) )^2 + 2 * (eps() - t(f) ) * v(f)))  |" + 
" (v(f) + a(f) * (eps() - t(f)) <= 0  & " +
" 2 * B() * a(f)^2 * x(f) - B() * v(f)^2 * a(f)   < 2 * B() * a(f)^2 * x(f) + a(f)^2 * v(f)^2   ))  "
 )



val instT =   instantiatebyT(St("C")) (List(("i", List("f", "l")), 
                                            ("f", List("f")), 
                                            ("l", List("l"))))


val tyltct = composelistT(
  hpalpha1T*,
  tryruleT(diffStrengthen(
    parseFormula(
      "eps() > 0 & A() > 0 & B() > 0 &" +
      "(forall i : C. (  " + 
      "t(i) >= 0 & a(i) >= -B()))" )))<(
        
        // initially valid
        composelistT(
          (alphaT | betaT | tryruleT(close))*,
          instantiatebyT(St("C"))(List(("i", List("i")))),
          alleasyT
        ),

        // invariant
        composelistT(
          (alphaT | betaT | tryruleT(close))*,
          hidethencloseT
        ),

        // strengthened
        tryruleT(diffStrengthen(diffinv))< (
           
          //initially valid
          composelistT(
            alphaT*,
            instantiatebyselfT(St("C"))*,
            alleasyT
          ),

          // invariant
          composelistT(
            alphaT*,
            instantiatebyT(St("C"))(List(("i", List("l", "f"))))*,
            alphaT*,
            instantiatebyT(St("C"))(List(("i", List("l"))))*,
            tryruleT(andRight)<(
              composelistT(tryruleT(andRight)*, tryruleT(close)),
              composelistT(nullarizeT*, alleasyT)
            )
          ),

          // strengthened
          composelistT(
            diffsolveT(RightP(0),Endpoint),
            hpalpha1T*,
            tryruleT(andRight) <(
              tryruleT(andRight) <(
                alleasyT,
                composelistT(
                  alphaT*,
                  instantiatebyselfT(St("C"))*,
                  alphaT*,
                  instantiatebyselfT(St("C"))*,
                  nullarizeT*,
                  hidethencloseT
                )
              ),
              composelistT(
                alphaT*,
                instT*,
                alphaT*,
                instT*,
                substT*,
                impleftknownT*,
                alphaT*,
                dedupT*,
                tryruleT(andRight)<(
                  composelistT(
                    // brittle!
                    tryruleatT(hide)(LeftP(0)),
                    tryruleT(impLeft)< (
                      composelistT(
                        alphaT*,
                        tryruleT(orLeft)<(
                          composelistT(
                            alphaT*,
                            okcuttct<(
                              composelistT(
                                alphaT*,
                                nullarizeT*,
                                okcuttct2<(
                                  composelistT(
                                    hidematchT(List(okcuttctfm1)),
                                    alleasyT
                                  ),
                                  composelistT(
                                    hidenotmatchT(List(okcuttct2fm1, 
                                                       okcuttct2fm2,
                                                       okcuttctfm2))*,
                                    alleasyT
                                  )
                                )
                              ),
                              composelistT(
                                nullarizeT*,
                                hidehasfnT("t")*,
                                hidehasfnT("id")*,
                                hidehasfnT("eps")*,
                                alleasyT
                              )
                            )
                          ),
                          composelistT(
                            alphaT*,
                            nullarizeT*,
                            alleasyT
                          )
                        )
                      ),
                      alleasyT
                    )
                  ),
                  alleasyT
                )
              )
            )
          )
        )
      )
  )





val deletetct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalpha1T*,
          instantiatebyT(St("C"))(List(("i", List("i")), ("j", List("i")))),
          nullarizeT*,
          alleasyT
        )
      ),
      composelistT(
        hpalpha1T*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("j", List("f","l"))))*,
        impleftgoalT,
        tryruleT(impLeft)*,
        alleasyT
      )
    )
  )

val createtct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalpha1T*,
          instantiatebyT(St("C"))(List(("i", List("i")), 
                                       ("j", List("i"))))*,
          tryruleT( impLeft)*, 
          alphaT*,
          substT*,
          nullarizeT*,
          alleasyT
        )
      ),
      composelistT(
        hpalpha1T*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("j", List("f","l"))))*,
        cutT(StandardKeepCut,
             parseFormula("~ F = N ==> T1 = T2"), 
             parseFormula("~ F = N")) < (
               composelistT(
                 vacuousT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 substT*,
                 nullarizeT*,
                 hidethencloseT
               ),
               composelistT(
                 impleftknownT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 substT*,
                 nullarizeT*,
                 hidethencloseT
               )
             )
      )
    )
  )

val controltct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalpha1T*,
          instantiatebyT(St("C"))(List(("i", List("i")), 
                                       ("j", List("i"))))*,
          tryruleT( impLeft)*, 
          alphaT*,
          substT*,
          nullarizeT*,
          hidethencloseT
        )
      ),
      composelistT(
        hpalpha1T*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("j", List("f","l"))))*,
        cutT(StandardKeepCut,
             parseFormula("~ F = N ==> T1 = T2"), 
             parseFormula("~ F = N")) < (
               composelistT(
                 vacuousT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 instantiatebyT(St("C"))(List(("f", List("f")),
                                              ("l", List("l")),
                                              ("j", List("f","l"))))*,
                 substT*,
                 nullarizeT*,
                 hidethencloseT
               ),
               composelistT(
                 impleftknownT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 substT*,
                 nullarizeT*,
                 hidethencloseT
               )
             )
      )
    )
  )

val loopinv = parseFormula(
  "eps() > 0 & A() > 0 & B() > 0 & " +
  "(forall i : C. (  a(i) >= -B() & v(i) >= 0 & " + 
  "t(i) >= 0 & t(i) <= eps()   )) & " +
  "(forall f : C. forall l : C. " +
   "(e(f) = 1 & e(l) = 1 & id(f) <= id(l))  ==> " +
" x(f) < x(l) & " + 
"  ((v(f) + a(f) * (eps() - t(f)) >= 0 &  " +
"2 * B() *  x(l)  > 2 *  B() * x(f) + v(f)^2 - v(l)^2 " +
     " + (a(f) + B()) * (a(f) * (eps() - t(f) )^2 + 2 * (eps() - t(f) ) * v(f)))  |" + 
" (v(f) + a(f) * (eps() - t(f)) <= 0  &  " +
" 2 * B() * a(f)^2 * x(f) - B() * v(f)^2 * a(f)   <  2 * B() * a(f)^2 * x(f) + a(f)^2 * v(f)^2   )))  "
 )



val starttct = 
  tryruleT(loopInduction(loopinv))<(
    easywithforallsT(St("C")),
    composelistT(
      hpalpha1T*,
      tryruleT(andRight)<(
        composelistT(
          tryruleT(choose),
          tryruleT(andRight)<(
            composelistT(
              tryruleT(choose),
              tryruleT(andRight)<(
                deletetct,
                createtct)),
        // control
            controltct)
        ),
        //dynamics
        tyltct
      )
    ),
    // post condition
    composelistT(
      hpalphaT*,
      instantiatebyT(St("C"))
                    (List(("i", List("f", "l")), 
                          ("f", List("f")), 
                          ("l", List("l"))))*,
      nullarizeT*,
      alleasyT
      
      
    )
  )


dl('gotoroot)
dl('tactic, starttct)
