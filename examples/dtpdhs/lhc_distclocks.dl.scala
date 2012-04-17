
object Script { 

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
  hpalphaT*,
  tryruleT(diffStrengthen(
    parseFormula(
      "eps() > 0 & B() > 0 &" +
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
            hpalphaT*,
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
                                    hidethencloseT
                                  ),
                                  composelistT(
                                    hidenotmatchT(List(okcuttct2fm1, 
                                                       okcuttct2fm2,
                                                       okcuttctfm2))*,
                                    hidethencloseT
                                  )
                                )
                              ),
                              composelistT(
                                nullarizeT*,
                                hidehasfnT("t")*,
                                hidehasfnT("id")*,
                                hidehasfnT("eps")*,
                                hidethencloseT
                              )
                            )
                          ),
                          composelistT(
                            alphaT*,
                            // get rid of all formulas with t(l$XX)
                            ( new Tactic("") {
                              import Nodes._
                               def apply(nd: OrNode) = {
                                 val Sequent(sig,s,c) = nd.goal
                                 sig.keys.toList.filter(k => Prover.ununiqify(k) == "l")
                                  match {
                                    case List(lname) =>
                                       val matches : Formula => Boolean = fm => 
                                            (Prover.hasFn_Formula(lname, fm) &&
                                             Prover.hasFn_Formula("t", fm))
                                       tryrulepredT(hide)(matches)(nd)
                                    case _ => None
                                  }
                               }
                              }
                            )*, 
                            
                            nullarizeT*,
                            hidehasfnT("id")*,
                            hidehasfnT("A")*,
                            cutdiffinv2,
                            hidethencloseT
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
    hpalphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalphaT*,
          instantiatebyT(St("C"))(List(("i", List("i")), ("j", List("i")))),
          tryruleT( impLeft)*, 
          alphaT*,
          substT*,
          nullarizeT*,
          (nonarithcloseT | alphaT | betaT )*,
          hidethencloseT
        )
      ),
      composelistT(
        hpalphaT*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("j", List("f","l")),
                                     ("i", List("f", "l"))))*,
        alphaT*,
        nonarithcloseT*,
        cutT(StandardKeepCut,
             parseFormula("~ F = N ==> T1 = T2"), 
             parseFormula("~ F = N")) < (
               composelistT(
                 vacuousT*,
                 alphaT*,
                 cutT(StandardKeepCut,
                      parseFormula("~ L = N ==> T1 = T2"), 
                      parseFormula("~ L = N")) < (
                        composelistT(
                          vacuousT*,
                          alphaT*,
                          substT*,
                          nonarithcloseT
                        ),
                        composelistT(
                          alphaT*,
                          substT,
                          substT,
                          hidethencloseT

                        )
                      )

               ),
               composelistT(
                 impleftknownT*,
                 cutT(StandardKeepCut,
                      parseFormula("~ L = N ==> T1 = T2"), 
                      parseFormula("~ L = N")) < (
                        composelistT(
                          vacuousT*,
                          alphaT*,
                          substT*,
                          nullarizeT*,
                          (nonarithcloseT | alphaT | betaT )*,
                          hidethencloseT
                        ),
                        composelistT(
                          alphaT*,
                          substT*,
                          nullarizeT*,
                          (nonarithcloseT | alphaT | betaT )*,
                          hidethencloseT
                        )
                      )
               )
             )
      )
    )
  )
 
val createtct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalphaT*,
          instantiatebyT(St("C"))(List(("i", List("i")), 
                                       ("j", List("i"))))*,
          tryruleT( impLeft)*, 
          alphaT*,
          substT*,
          nullarizeT*,
          (nonarithcloseT | alphaT | betaT )*,
          hidethencloseT
        )
      ),
      composelistT(
        (nonarithcloseT | hpalphaT)*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("i", List("f", "l")),
                                     ("j", List("f","l"))))*,
        alphaT*,
        nonarithcloseT*,
        cutT(StandardKeepCut,
             parseFormula("~ F = N ==> T1 = T2"), 
             parseFormula("~ F = N")) < (
               composelistT(
                 vacuousT*,
                 alphaT*,
                 cutT(StandardKeepCut,
                      parseFormula("~ L = N ==> T1 = T2"), 
                      parseFormula("~ L = N")) < (
                        composelistT(
                          vacuousT*,
                          alphaT*,
                          substT*,
                          nonarithcloseT
                        ),
                        composelistT(
                          impleftknownT*,
                          alphaT*,
                          substT*,
                          nullarizeT*,
                          tryruleatT(hide)(LeftP(0)),
                          tryruleatT(hide)(LeftP(8)),
                          (nonarithcloseT | alphaT | betaT | commuteequalsT)*,
                          hidethencloseT

                        )
                      )
               ),
               composelistT(
                 impleftknownT*,
                 cutT(StandardKeepCut,
                      parseFormula("~ L = N ==> T1 = T2"), 
                      parseFormula("~ L = N")) < (
                        composelistT(
                          vacuousT*,
                          alphaT*,
                          substT*,
                          nullarizeT*,
                          tryruleatT(hide)(LeftP(0)),
                          tryruleatT(hide)(LeftP(9)),
                          (nonarithcloseT | alphaT | betaT | commuteequalsT)*,
                          hidethencloseT
                        ),
                        composelistT(
                          impleftknownT*,
                          substT*,
                          nullarizeT*,
                          tryruleatT(hide)(LeftP(11)),
                          tryruleatT(hide)(LeftP(11)),
                          (nonarithcloseT | alphaT | betaT | commuteequalsT)*,
                          hidethencloseT


                         
                        )
                      )
               )
             )
      )))

val controltct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        alleasyT,
        composelistT(
          hpalphaT*,
          instantiatebyT(St("C"))(List(("i", List("i")), 
                                       ("j", List("i"))))*,
          tryruleT( impLeft)*, 
          alphaT*,
          substT*,
          nullarizeT*,
          (nonarithcloseT | alphaT | betaT )*,
          hidethencloseT
        )
      ),
      composelistT(
        hpalphaT*,
        instantiatebyT(St("C"))(List(("f", List("f")),
                                     ("l", List("l")),
                                     ("j", List("f","l")),
                                     ("i", List("f","l"))
                                   ))*,
        cutT(StandardKeepCut,
             parseFormula("~ F = N ==> T1 = T2"), 
             parseFormula("~ F = N")) < (
               composelistT(
                 vacuousT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 tryruleT(orLeft)*,
                 instantiatebyT(St("C"))(List(("f", List("f")),
                                              ("l", List("l")),
                                              ("j", List("f","l"))))*,
                 substT*,
                 nullarizeT*,
                 (nonarithcloseT | alphaT | betaT )*,
                 hidethencloseT
               ),
               composelistT(
                 impleftknownT*,
                 tryruleT( impLeft)*,
                 alphaT*,
                 substT*,
                 nullarizeT*,
                 (nonarithcloseT | alphaT | betaT )*,
                 hidethencloseT
               )
             )
      )
    )
  )

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
      hpalphaT*,
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

val main = starttct

}
