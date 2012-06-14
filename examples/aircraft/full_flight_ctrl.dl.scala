object Script {


val maininv =
  parseFormula (
   "forall i : C ." +
      "forall j : C ." +
        "( i /= j ==> " +
            "(disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2 >= (4*minr() + protectedzone())^2)")


val inv1 =
  parseFormula (
   "forall k : C . " +
    "(ca(k) = 0 | ca(k) = 1) &" +
    "d1(k) * ca(k) = -om(k) * (x2(k) - c2(k) ) * ca(k) &" +
    "d2(k) * ca(k) = om(k) * (x1(k) - c1(k) ) * ca(k) &" +
    "((c1(k) - x1(k))^2 + (c2(k) - x2(k))^2) * ca(k) = minr()^2 * ca(k) &"+
    "((c1(k) - disc1(k))^2 + (c2(k) - disc2(k))^2) * ca(k) = minr()^2 * ca(k) & "+
    "(1 - ca(k)) * x1(k) = (1 - ca(k)) * disc1(k) &"+
    "(1 - ca(k)) * x2(k) = (1 - ca(k)) * disc2(k)")

val constinv =
  parseFormula (
    "minr() > 0 & protectedzone() > 0"
 )

val cut1 = cutT(
  StandardKeepCut,
  parseFormula("~ I = II  ==> D1 = D2"),
  parseFormula("~I = II"))


val doasgns =
  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(List (("i", List("k")),
                                  ("k", List("k")),
                                  ("j", List("k")))),
    hideunivsT(St("C")),
    cut1<(
      composelistT(
        alphaT*,
        substT,
        vacuousT*,
        nullarizeT*,
        easiestT
      ),
      composelistT(
        (tryruleT(impLeft) & (tryruleT(close)*))*,
        alleasyT
      )
    )
  )


val entercatct =
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        tryruleT(close),
        doasgns
      ),
      (tryruleT(close) | alphaT | betaT)*
    )
  )


val exitcatct =
   composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        tryruleT(close),
        doasgns
      ),
      (tryruleT(close) | alphaT | betaT)*
    )
)

val controltct = composelistT(hpalphaT*,
                              tryruleT(andRight)<(entercatct, exitcatct))

val diffinv1 = parseFormula("forall k : C . (ca(k) = 0 | ca(k) = 1)")

val diffinv2 =
  parseFormula(
   "forall k : C . " +
    "d1(k) * ca(k) = -om(k) * (x2(k) - c2(k) ) * ca(k) &" +
    "d2(k) * ca(k) = om(k) * (x1(k) - c1(k) ) * ca(k) &" +
    "(1 - ca(k)) * x1(k) = (1 - ca(k)) * disc1(k) &"+
    "(1 - ca(k)) * x2(k) = (1 - ca(k)) * disc2(k)")

val diffinv3 =
  parseFormula(
    "forall k : C. " +
    "((c1(k) - x1(k))^2 + (c2(k) - x2(k))^2) * ca(k) = minr()^2 * ca(k) &"+
    "((c1(k) - disc1(k))^2 + (c2(k) - disc2(k))^2) * ca(k) = minr()^2 * ca(k)  ")

val diffinv4 =
  parseFormula (
   "forall i : C ." +
     "forall j : C ." +
      "(i /= j  ==> " +
       "((disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2) * ca(i) * ca(j) >= ((4*minr() + protectedzone())^2) * ca(i) * ca(j))")

val di1tct = composelistT(
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
   tryruleT(diffStrengthen(constinv))<(
     easiestT,
     easiestT,
     tryruleT(diffStrengthen(diffinv1))<(
       di1tct,
       easiestT,
       tryruleT(diffStrengthen(diffinv2))<(
         di1tct,
         di2tct,
         tryruleT(diffStrengthen(diffinv3))<(
           di1tct,
           di2tct,
           tryruleT(diffStrengthen(diffinv4))<(
             composelistT(
               tryruleatT(hide)(LeftP(0)),
               (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                      ("j", List("j")),
                                                      ("k", List("i", "j")))))*,
               nullarizeT*,
               tryruleT(impLeft)<(
                 (tryruleunifyT(hide)(parseFormula("I /= J"))   & easiestT),
                 easiestT
               )
             ),
             composelistT(
               alphaT*,
               (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                      ("j", List("j")),
                                                      ("k", List("i", "j")))))*,
               nullarizeT*,
               hidethencloseT
             ),
             composelistT(
               tryruleT(diffClose),
               tryruleT(andRight)<(
                 tryruleT(andRight)<(
                   composelistT(
                     alphaT*,
                     (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                            ("j", List("j")),
                                                            ("k", List("i", "j")))))*,
                     nullarizeT*,
                     (tryruleT(close) | alphaT | betaT | hidethencloseT)*

                   ),
                   composelistT(
                     alphaT*,
                     (alphaT | instantiatebyT(St("C"))(List(("i", List("k")),
                                                            ("j", List("k")),
                                                            ("k", List("k")))))*,
                     easiestT
                   )
                 ),
                 (alphaT | tryruleT(close) | instantiatebyT(St("C"))(List(("i", List("ii")))) | betaT)*
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

val simpcut =
  cutT(DirectedCut,
       parseFormula(" (1 - 0) * X  = (1 - 0) * D"),
       parseFormula("X  = D"))



val postors =
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(
        ((nullarizeT*) & hidethencloseT ),
        composelistT(
          substT*,
          simpcut<(
            ((nullarizeT*) &  arithT),
              simpcut<(
              ((nullarizeT*) &  arithT),
              composelistT(
                substT*,
                cutT(
                  DirectedCut,
                  parseFormula(" (disc1(I) - disc1(J))^2 + (disc2(I) - disc2(J))^2 >= ( 4 * R  + P)^2"),
                  parseFormula(" (c1(J) - disc1(I))^2 + (c2(J) - disc2(I))^2 >= ( 2 * R  + P)^2")
                )<(
                  composelistT(
                    nullarizeT*,
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    arithT
                  ),
                  composelistT(
                    nullarizeT*,
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(3)),
                    tryruleatT(hide)(LeftP(4)),
                    arithT
                  )
                )
              )
            )
          )
        )
      ),
      tryruleT(orLeft)<(
        composelistT(
          substT*,
          simpcut<(
            ((nullarizeT*) &  arithT),
              simpcut<(
                ((nullarizeT*) &  arithT),
                composelistT(
                  substT*,
                  tryruleatT(hide)(LeftP(3)),
                  tryruleatT(hide)(LeftP(3)),
                  tryruleatT(hide)(LeftP(5)),
                  tryruleatT(hide)(LeftP(5)),
                  tryruleatT(hide)(LeftP(5)),
                  tryruleatT(hide)(LeftP(5)),
                  cutT(
                    DirectedCut,
                    parseFormula(" (disc1(I) - disc1(J))^2 + (disc2(I) - disc2(J))^2 >= ( 4 * R  + P)^2"),
                    parseFormula(" (c1(I) - disc1(J))^2 + (c2(I) - disc2(J))^2 >= ( 2 * R  + P)^2")
                  )<(
                    composelistT(
                      nullarizeT*,
                      tryruleatT(hide)(LeftP(3)),
                      arithT
                    ),
                    composelistT(
                      nullarizeT*,
                      tryruleatT(hide)(LeftP(4)),
                      arithT
                    )
                  )
                )
              )
          )
        ),
        composelistT(
          substT*,
          tryruleatT(hide)(LeftP(3)),
          tryruleatT(hide)(LeftP(3)),
          tryruleatT(hide)(LeftP(5)),
          tryruleatT(hide)(LeftP(5)),
          cutT(
            DirectedCut,
            parseFormula(" (disc1(I) - disc1(J))^2 + (disc2(I) - disc2(J))^2 >= ( 4 * R  + P)^2"),
            parseFormula(" (c1(J) - disc1(I))^2 + (c2(J) - disc2(I))^2 >= ( 3 * R  + P)^2")
          )<(
            composelistT(
              nullarizeT*,
              tryruleatT(hide)(LeftP(3)),
              tryruleatT(hide)(LeftP(3)),
              tryruleatT(hide)(LeftP(3)),
              arithT
            ),
            cutT(
              DirectedCut,
              parseFormula(" (c1(J) - disc1(I))^2 + (c2(J) - disc2(I))^2 >= ( 3 * R  + P)^2"),
              parseFormula(" (x1(J) - disc1(I))^2 + (x2(J) - disc2(I))^2 >= ( 2 * R  + P)^2")
            )<(
              composelistT(
                nullarizeT*,
                tryruleatT(hide)(LeftP(3)),
                tryruleatT(hide)(LeftP(3)),
                tryruleatT(hide)(LeftP(4)),
                arithT
              ),
              cutT(
                DirectedCut,
                parseFormula(" (x1(J) - disc1(I))^2 + (x2(J) - disc2(I))^2 >= ( 2 * R  + P)^2"),
                parseFormula(" (c1(I) - x1(J))^2 + (c2(I) - x2(J) )^2 >= (1 * R  + P)^2")
              )<(
                composelistT(
                  nullarizeT*,
                  tryruleatT(hide)(LeftP(3)),
                  tryruleatT(hide)(LeftP(4)),
                  tryruleatT(hide)(LeftP(4)),

                  tryruleatT(hide)(LeftP(4)),
                  tryruleatT(hide)(LeftP(4)),
                  tryruleatT(hide)(LeftP(4)),
                  tryruleatT(hide)(LeftP(4)),
                  cutT(
                    StandardCut,
                    parseFormula(" ((C1 - D1)^2 + (C2 - D2)^2) * 1 = ( R )^2 * 1"),
                    parseFormula(" ((C1 - D1)^2 + (C2 - D2)^2) * 1 = ( R )^2 * 1")
                  ) < (
                    tryruleT(close),
                    cutT(
                      StandardCut,
                      parseFormula("minr() > 0"),
                      parseFormula("minr() > 0")
                    )<(
                      tryruleT(close),
                      cutT(
                        StandardCut,
                        parseFormula("protectedzone() > 0"),
                        parseFormula("protectedzone() > 0")
                      )<(
                        tryruleT(close),
                        composelistT(
                          tryruleatT(hide)(LeftP(3)),
                          tryruleatT(hide)(LeftP(3)),
                          tryruleatT(hide)(LeftP(4)),
                          arithT
                        )
                      )
                    )

                  )
                ),
                cutT(
                  DirectedCut,
                  parseFormula(" (c1(I) - x1(J))^2 + (c2(I) - x2(J) )^2 >= (1 * R + P)^2"),
                  parseFormula(" (x1(I) - x1(J))^2 + (x2(I) - x2(J) )^2 >= (P)^2")
                )<(
                  composelistT(
                    nullarizeT*,
                    tryruleatT(hide)(LeftP(4)),
                    tryruleatT(hide)(LeftP(4)),
                    tryruleatT(hide)(LeftP(4)),
                    tryruleatT(hide)(LeftP(6)),
                    tryruleatT(hide)(LeftP(6)),
                    tryruleatT(hide)(LeftP(5)),
// I get a weird AWT error if I uncomment this.
//                  tryruleatT(hide)(LeftP(4)),
                    arithT
                  ),
                  tryruleT(close)
                )
              )
            )
          )
        )
      )
    )




val postconditiontct =
  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(List(("i", List("i")),
                                 ("j", List("j")),
                                 ("k", List("i", "j"))))*,
    alphaT*,
    // The things I do to make Mathematica happy...
    // Apparently it helps to move these assumptions to the front.
    tryruleunifyT(reorder)(parseFormula("minr() > Y")),
    tryruleunifyT(reorder)(parseFormula("protectedzone() > Y")),
    tryruleT(impLeft)<(
      (tryruleunifyT(hide)(parseFormula("I /= J")) & postors),
      easiestT
    )
)


val starttct =
   tryruleT(loopInduction(Binop(And, Binop(And,maininv, inv1), constinv)))<(
     easiestT,
     indtct,
     postconditiontct)

val main = starttct

val trivial =
   composelistT(
     hideallbutT(List(LeftP(0), LeftP(2), LeftP(3))),
     instantiatebyT(St("C"))(List(("i", List("ii")),
                                  ("j", List("ii"))))*,
     nullarizeT*,
     easiestT
   )

}
