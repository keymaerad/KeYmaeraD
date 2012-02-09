object Script {


val maininv = 
  parseFormula (
   "forall i : C ." +
         "forall j : C ."+
            "(disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2 >= (4*minr() + protectedzone())^2")


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
    hpalpha1T*,
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
    hpalpha1T*,
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
      "forall j : C ."+
       "((disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2) * ca(i) * ca(j) >= ((4*minr() + protectedzone())^2) * ca(i) * ca(j)")

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
    arithT
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
               easiestT*
             ),
             composelistT(
               (alphaT | instantiatebyT(St("C"))(List(("i", List("i")),
                                                      ("j", List("j")),
                                                      ("k", List("i", "j")))))*,
               nullarizeT*,
               easiestT
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
                     easiestT
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

val postconditiontct = 
  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(List(("i", List("i")),
                                 ("j", List("j")),
                                 ("k", List("i", "j"))))*,
    alphaT*,
    nullarizeT*,
    (alphaT | betaT)*,
    substT*

  )

val starttct =
   tryruleT(loopInduction(Binop(And, Binop(And,maininv, inv1), constinv)))<(
     easiestT,
     indtct,
     postconditiontct)

val main = starttct

}

