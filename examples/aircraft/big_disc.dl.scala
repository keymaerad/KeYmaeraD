object Script {

val maininv = 
  parseFormula (
    "forall i : C ." +
     "forall j : C ." +
      "( i /= j ==> " + 
      "(bigdisc1(i) - bigdisc1(j))^2 + (bigdisc2(i) - bigdisc2(j))^2 >="  +
       "(2 * minr(i) + 2 * minr(j) + protectedzone())^2)")

val inv1 = 
  parseFormula (
    "forall i : C . (  " +
     "(ca(i) = 0 | ca(i) = 1) " +
     " & (discside(i) = -1 | discside(i) = 1) " +
     "& ((-discside(i) * minr(i) * d2(i) + x1(i) - bigdisc1(i))^2" +
         " + (discside(i) * minr(i) * d1(i) + x2(i) - bigdisc2(i))^2 <= minr(i)^2))" +
     "& (1 - ca(i)) * bigdisc1(i) = (1 - ca(i)) * x1(i)" +
     "& (1 - ca(i)) * bigdisc2(i) = (1 - ca(i)) * x2(i)"
  )

val constinv1 = 
  parseFormula (
   "protectedzone() > 0  & " +
   "(forall i : C . minr(i) > 0 & d1(i)^2 + d2(i)^2 = 1)"
 )

val constinv2 = 
  parseFormula (
   "(forall i : C . v(i) > 0 & maxom(i) > 0 & maxom(i) * minr(i) = v(i))" 
 )

val cut1 = cutT(
  StandardKeepCut,
  parseFormula("~ I = II  ==> D1 = D2"),
  parseFormula("~I = II"))

val incatct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      composelistT(
        hpalphaT*,
        tryruleT(andRight)<(
          easiestT,
          tryruleT(andRight)<(
            easiestT,
            composelistT(
              alphaT*,
              instantiatebyT(St("C"))(List(("i", List("i")),
                                           ("j", List("i")))),
              cut1<(
                alleasyT,
                tryruleunifyT(impLeft)(parseFormula("~ I = II  ==> D1 = D2"))<(
                  composelistT(
                    substT*,
                    (nonarithcloseT | tryruleT(impLeft) |
                     ((nullarizeT*) & hidethencloseT ) )*
                  ),
                  nonarithcloseT
                )
              )
            )
          )
        )
      ),
      easiestT
     )
)

val outcatct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      composelistT(
        hpalphaT*,
        tryruleT(andRight)<(
          easiestT,
          composelistT(
            hpalphaT*,
            tryruleT(andRight)<(
              easiestT,
              tryruleT(andRight)<(
                easiestT,
                composelistT(
                  alphaT*,
                  instantiatebyT(St("C"))(List(("i", List("i")),
                                               ("j", List("i")))),
                  cut1<(
                    composelistT(
                      alphaT*,
                      substT*,
                      vacuousT*,
                      hideunivsT(St("C")),
                      nullarizeT*,
                      easiestT
                    ),
                    tryruleunifyT(impLeft)(parseFormula("~ I = II  ==> D1 = D2"))<(
                      alleasyT,
                      nonarithcloseT
                    )
                  )
                )
              )
            )
          )
        )
      ),
      composelistT(
        hpalphaT*,
        tryruleT(andRight)<(
          easiestT,
          tryruleT(andRight)<(
            easiestT,
            composelistT(
              alphaT*,
              instantiatebyT(St("C"))(List(("i", List("i")),
                                           ("j", List("i")))),
              cut1<(
                composelistT(
                  alphaT*,
                  substT*,
                  vacuousT*,
                  hideunivsT(St("C")),
                  nullarizeT*,
                  easiestT
                ),
                tryruleunifyT(impLeft)(parseFormula("~ I = II  ==> D1 = D2"))<(
                  tryruleunifyT(impLeft)(parseFormula("~ I = II  ==> D1 = D2"))<(
                    alleasyT,
                    nonarithcloseT
                  ),
                  nonarithcloseT
                )
              )
            )

          )
        )
      )
    )
)

val controltct = composelistT(hpalphaT*,
                              tryruleT(andRight)<(incatct, outcatct)
                             )

val diffinv1 =
 parseFormula("forall k : C . ((ca(k) = 0 | ca(k) = 1)  &" +
              " (discside(k) = -1 | discside(k) = 1   )) ")

val diffinv2 = 
  parseFormula(
   "forall k : C . " +
     "((1 - ca(k)) * bigdisc1(k) = (1 - ca(k)) * x1(k)" +
     "& (1 - ca(k)) * bigdisc2(k) = (1 - ca(k)) * x2(k))"
  )


val diffinv3 = 
  parseFormula (
    "forall i : C ." +
     "forall j : C ." +
      "( i /= j ==> " + 
      "((bigdisc1(i) - bigdisc1(j))^2 + " + 
       "(bigdisc2(i) - bigdisc2(j))^2) * ca(i) * ca(j) >="  +
       "(2 * minr(i) + 2 * minr(j) + protectedzone())^2  * ca(i) * ca(j) )")


val di1tct =
  composelistT(
    (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                           ("j", List("j")),
                                           ("k", List("i", "j")))))*,
    nullarizeT*,
    dedupT*,
    (nonarithcloseT | alphaT | betaT | substT | hidethencloseT)*
  )

val di2tct =  
  composelistT(
    alphaT*,
    (alphaT | instantiatebyT(St("C"))(List(("k", List("k")),
                                           ("i", List("k")),
                                           ("j", List("k")))))*,
    nullarizeT*,
    (nonarithcloseT | alphaT | betaT | substT | hidethencloseT)*

  )

val evolvetct = 
   tryruleT(diffStrengthen(Binop(And, constinv1, constinv2)))<(
     easiestT,
     composelistT(
       hideunivsT(St("C")),
       (nonarithcloseT | alphaT | betaT | nullarizeT | arithT)*
     ),
     tryruleT(diffStrengthen(diffinv1))<(
       di2tct,
       di2tct,
       tryruleT(diffStrengthen(diffinv2))<(
         di2tct,
         di2tct,
         tryruleT(diffStrengthen(diffinv3))<(
           di1tct,
           di1tct,
           composelistT(
             tryruleT(diffClose),
             tryruleT(andRight)<(
               composelistT(
                 instantiatebyT(St("C"))(List(("i", List("ii")))),
                 alphaT*,
                 easiestT
               ),
               tryruleT(andRight)<(
                 composelistT(
                   alphaT*,
                   (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                          ("k", List("i", "j")),
                                                          ("j", List("j")))))*,
                   (nonarithcloseT | alphaT | betaT | nullarizeT | substT | hidethencloseT)*
                 ),
                 composelistT(
                   alphaT*,
                   (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                          ("k", List("i")))))*,
                   easiestT
                 )
               )
             )
           )
         )
       )
     )
   )
val indtct =
  composelistT(hpalphaT*,
               tryruleT(andRight)<(controltct, evolvetct))

val cutfm = 
  parseFormula(
    "(-(discside(I) * minr(I) * d2(I)) + x1(I) - bigdisc1(I))^2 + " +
    "(discside(I) * minr(I) * d1(I) + x2(I) - bigdisc2(I))^2 <= minr(I)^2"
  )

val cutfm2 = 
  parseFormula(
    "(bigdisc1(I) - bigdisc1(J))^2 + (bigdisc2(I) - bigdisc2(J))^2 >= (2 * minr(I) + 2 * minr(J) + protectedzone())^2"
  )

val subcut =
        cutT(
          DirectedCut,
          cutfm,
          parseFormula(
            "(x1(I) - bigdisc1(I))^2 + " +
            "(x2(I) - bigdisc2(I))^2 <= 4 * minr(I)^2"
          )
        )

val postconditiontct = 
  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(List(("i", List("i", "j")),
                                 ("j", List("j"))))*,
    alphaT*,
    tryruleatT(hide)(LeftP(0)),
    tryruleT(impLeft)<(
      composelistT(
        tryruleunifyT(hide)(parseFormula("I /= J")),
        alphaT*,
        subcut<(
          composelistT(
            tryruleatT(hide)(LeftP(0)),
            tryruleatT(hide)(LeftP(7)),
            nullarizeT*,
            alleasyT
          ),
          subcut<(
            composelistT(
              tryruleatT(hide)(LeftP(0)),
              nullarizeT*,
              alleasyT
            ),
            composelistT(
              tryruleunifyT(hide)(parseFormula("ca(I) = 0 | ca(J) = 1 "))*,
              tryruleunifyT(hide)(parseFormula("DS = -1 | DS = 1 "))*,
              hideallbutT(List(LeftP(0), LeftP(1), LeftP(4), LeftP(4),
                               LeftP(13), LeftP(15), LeftP(17),
                               RightP(0))),
              cutT(
                StandardKeepCut,
                cutfm2,
                parseFormula("minr(I) > 0")
              )<(
                nonarithcloseT,
                cutT(
                  StandardKeepCut,
                  cutfm2,
                  parseFormula("minr(J) > 0")
                )<(
                  nonarithcloseT,
                  cutT(
                    StandardKeepCut,
                    cutfm2,
                    parseFormula("protectedzone() > 0")
                  )<(
                    nonarithcloseT,
                    composelistT(
                      tryruleatT(hide)(LeftP(6)),
                      tryruleatT(hide)(LeftP(6)),
                      tryruleatT(hide)(LeftP(6)),
                      cutT(
                        DirectedCut,
                        cutfm2,
                        parseFormula("(x1(I) - bigdisc1(J))^2 + (x2(I) - bigdisc2(J))^2 >= (2 * minr(J) + protectedzone())^2")
                      )<(
                        composelistT(
                          tryruleatT(hide)(LeftP(5)),
                          nullarizeT*,
                          arithT
                        ),
                        composelistT(
                          tryruleatT(hide)(LeftP(4)),
                          nullarizeT*,
                          arithT
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      ),
      easiestT
    )
  )

val starttct =
   tryruleT(loopInduction(Binop(And, Binop(And, constinv1, constinv2),
                                     Binop(And, maininv, inv1)
                              )))<(
     easiestT,
     indtct,
     postconditiontct)

val main = starttct

}
