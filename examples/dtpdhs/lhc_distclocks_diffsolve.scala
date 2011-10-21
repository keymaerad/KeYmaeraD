dl('load, "examples/dtpdhs/lhc_distclocks.dl")

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


val diffinv = parseFormula(
  "forall f : C. forall l : C. " +
   "(f /= l & e(f) = 1 & e(l) = 1 & id(f) <= id(l))  ==> " +
"  ( (v(f) + a(f) * (eps() - t(f)) >= 0 & " +
"2 * B() *  x(l)  > 2 *  B() * x(f) + v(f)^2 - v(l)^2 " +
     " + (a(f) + B()) * (a(f) * (eps() - t(f) )^2 + 2 * (eps() - t(f) ) * v(f)))  |" + 
" (v(f) + a(f) * (eps() - t(f)) < 0  & " +
" 2 * B() * a(f)^2 * x(f) - B() * a(f) * v(f)^2 < 2 * B() * a(f)^2 * x(l) + a(f)^2 * v(l)^2   ))  "
 )



val instT =   instantiatebyT(St("C")) (List(("i", List("f", "l")), 
                                            ("f", List("f")), 
                                            ("l", List("l"))))

val cutdiffinv2 = cutT(
  DirectedCut,
  parseFormula("2 * B() * A^2 * X1 - B() * A * V1^2 < "+
              "2 * B() * A^2 * X2 + A^2 * V2^2"),
  parseFormula("2 * B() * A * X1 - B() * V1^2 > "+
              "2 * B() * A * X2 + A * V2^2")
)


val tyltct = composelistT(
  hpalpha1T*,
  diffsolveT(RightP(0),Endpoint),
  hpalpha1T*,
  tryruleT(andRight)<(
    composelistT(
      nilT
    ),
    composelistT(
      alphaT*,
      instantiatebyT(St("C"))(List(("i", List("f", "l")),
                                   ("f", List("f")),
                                   ("l", List("l"))))*,
      alphaT*,
      tryruleT(impLeft)<(
        composelistT(
          alphaT*,
          nullarizeT*,
          substT*
        ),
        alleasyT
      )
    )
  )
)





val deletetct = nilT
 
val createtct = nilT

val controltct = nilT

val loopinv = parseFormula(
  "eps() > 0 & B() > 0 & " +
  "(forall i : C. (  a(i) >= -B() & v(i) >= 0 & " + 
  "t(i) >= 0 & t(i) <= eps()   )) & " +
  "(forall f : C. forall l : C. " +
   "(f /= l & e(f) = 1 & e(l) = 1 & id(f) <= id(l))  ==> " +
" x(f) < x(l) & " + 
"  ((v(f) + a(f) * (eps() - t(f)) >= 0 &  " +
"2 * B() *  x(l)  > 2 *  B() * x(f) + v(f)^2 - v(l)^2 " +
     " + (a(f) + B()) * (a(f) * (eps() - t(f) )^2 + 2 * (eps() - t(f) ) * v(f)))  |" + 
" (v(f) + a(f) * (eps() - t(f)) < 0  &  " +
" 2 * B() * a(f)^2 * x(f) - B() * a(f) * v(f)^2 < 2 * B() * a(f)^2 * x(l) + a(f)^2 * v(l)^2   )))  "
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
      tryruleT(directedCut(parseFormula(
         "forall f : C. forall l : C. "+
         "(f /= l & e(f) = 1 & e(l) = 1 & id(f) <= id(l) )  ==> x(f) < x(l)")))<(
           composelistT(
             hpalphaT*,
             instantiatebyT(St("C"))
               (List(("i", List("f", "l")), 
                     ("f", List("f")), 
                     ("l", List("l"))))*,
              nullarizeT*,
              (nonarithcloseT | alphaT | betaT)*,
              hidethencloseT),
           composelistT(
             hpalphaT*,
             instantiatebyT(St("C"))
               (List(("f", List("f", "l")), 
                     ("l", List("f", "l"))))*,
             (nonarithcloseT | alphaT | betaT | commuteequalsT)*,
             nullarizeT*,
             hidethencloseT

           )
         )
    )
  )    


dl('gotoroot)
dl('tactic, starttct)
