object Script {


val maininv = 
  parseFormula (
    "forall i : C ." +
     "forall j : C ." +
      "( i /= j ==> " + 
      "(bigdisc1(i) - bigdisc1(j))^2 + (bigdisc2(i) - bigdisc2(j))^2 >="  +
       "(minr(i) + minr(j) + protectedzone())^2)")


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
    hpalpha1T*,
    tryruleT(andRight)<(
      composelistT(
        hpalpha1T*,
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
    hpalpha1T*,
    tryruleT(andRight)<(
      composelistT(
        hpalpha1T*,
        tryruleT(andRight)<(
          easiestT,
          composelistT(
            hpalpha1T*,
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
        hpalpha1T*,
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
    " om(k) * ca(k) = maxom(k) * discside(k) * ca(k)"
  )


val diffinv4 = 
  parseFormula (
    "forall i : C ." +
     "forall j : C ." +
      "( i /= j ==> " + 
      "((discside(j) * (minr(j) * d2(j)) - discside(i) * (minr(i) * d2(i)) + " +
      "x1(i) - x1(j) )^2 +" + 
      "(discside(i) * (minr(i) * d1(i)) - discside(j) * (minr(j) * d1(j)) + " + 
      "x2(i) - x2(j))^2) * ca(i) * ca(j) >=" +
      "(minr(i) + minr(j) + protectedzone())^2 * ca(i) * ca(j))")


val di1tct =  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(List(("k", List("k")))),
    hideunivsT(St("C")),
    easiestT
   )

val di2tct =  
  composelistT(
    alphaT*,
    (alphaT | instantiatebyT(St("C"))(List(("k", List("k")),
                                           ("i", List("k")),
                                           ("j", List("k")))))*,
    nullarizeT*,
    hidethencloseT
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
         tryruleT(diffStrengthen(diffinv4))<(
           composelistT(
             (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                    ("j", List("j")),
                                                    ("k", List("i", "j")))))*,
             nullarizeT*,
             (nonarithcloseT | alphaT | betaT | substT  | hidethencloseT)*
           ),
           composelistT(
             (alphaT | instantiatebyT(St("C"))(List(("i", List("i", "j")),
                                                    ("j", List("j")),
                                                    ("k", List("i", "j")))))*,
             nullarizeT*,
             dedupT*,
             (nonarithcloseT | alphaT | betaT | substT | hidethencloseT)*
           ),
           composelistT(
             tryruleT(diffClose),
             tryruleT(andRight)<(
               tryruleT(andRight)<(
                 tryruleT(andRight)<(
                   (nonarithcloseT | alphaT |
                    instantiatebyT(St("C"))(List(("i", List("ii")),
                                                 ("j", List("jj")))))*,
                   (nonarithcloseT | alphaT |
                    instantiatebyT(St("C"))(List(("i", List("i")),
                                                 ("j", List("i")))))*
                 ),
                 (nonarithcloseT | alphaT |
                    instantiatebyT(St("C"))(List(("i", List("i")),
                                                 ("j", List("i")))))*
               ),
               tryruleT(andRight)<(
                 composelistT(
                   alphaT*,
                   (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                          ("j", List("j")),
                                                          ("k", List("i", "j")))))*,
                   nullarizeT*,
                   (nonarithcloseT | alphaT | betaT | substT | hidethencloseT)*
                 ),
                 composelistT(
                   alphaT*,
                   tryruleT(andRight)<(
                     (nonarithcloseT | tryruleT(andLeft) |
                      instantiatebyT(St("C"))(List(("i", List("i")),
                                                   ("k", List("i")),
                                                   ("j", List("i")))))*,
                     (nonarithcloseT | alphaT |
                      instantiatebyT(St("C"))(List(("i", List("i")),
                                                   ("k", List("i")),
                                                   ("j", List("i")))))*
                   )
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
    "(discside(J) * (minr(J) * d2(J)) - discside(I) * (minr(I) * d2(I)) + (x1(I) - x1(J)))^2 " +
    "+(discside(I) * (minr(I) * d1(I)) - discside(J) * (minr(J) * d1(J)) + (x2(I) - x2(J)))^2" +
    ">= (minr(I) + minr(J) + protectedzone())^2")

val postconditiontct = 
  composelistT(
    alphaT*,
//    hideallbutT(List(LeftP(0), LeftP(1), LeftP(2), LeftP(4), RightP(0))),
    instantiatebyT(St("C"))(List(("i", List("i", "j")),
                                 ("j", List("j"))))*,
    alphaT*,
    tryruleunifyT(hide)(parseFormula("ca(I) = 0 | ca(J) = 1 "))*,
    tryruleatT(hide)(LeftP(0)),
    tryruleT(impLeft)<(
      composelistT(
        tryruleunifyT(hide)(parseFormula("I /= J")),
        alphaT*,
        cutT(
          DirectedCut,
          cutfm,
          parseFormula(
            "(discside(J) * (minr(J) * d2(J))  + (x1(I) - x1(J)))^2 " +
            "+ ( - discside(J) * (minr(J) * d1(J)) + (x2(I) - x2(J)))^2" +
            ">= (minr(J) + protectedzone())^2")
        )<(
          composelistT(
            cutT(
              StandardCut,
              cutfm,
              parseFormula("(minr(I) * d2(I))^2 + (minr(I) * d1(I))^2 = minr(I)^2")
            )<(
              composelistT(
                nullarizeT*,
                easiestT
              ),
              cutT(
                StandardCut,
                cutfm,
                parseFormula("minr(I) > 0") )<( 
                  easiestT,
                  cutT(
                    StandardCut,
                    cutfm,
                    parseFormula("minr(J) > 0") )<( 
                      easiestT,
                      cutT(
                        StandardCut,
                        parseFormula("protectedzone() > 0"),
                        parseFormula("protectedzone() > 0"))<(
                          easiestT,
                          composelistT(
                            tryruleatT(hide)(LeftP(6)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            tryruleatT(hide)(LeftP(7)),
                            unsubT(
                              parseFormula(
                                "(D1 * Y - D2 * Z + C)^2 " +
                                "+ (D3 * A - D4 * B + D)^2" +
                                ">= (X)^2"),
                              List(Var("A"), 
                                   Var("B"), 
                                   Var("C"), 
                                   Var("D"),
                                   Var("Y"),
                                   Var("Z"))),
                            nullarizeT*
                            
                          )
                        )
                    )
                )
            )
          ),
          composelistT(
            nullarizeT*,
            easiestT
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

