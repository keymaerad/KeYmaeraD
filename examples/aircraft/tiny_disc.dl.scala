object Script {


val maininv = 
  parseFormula (
    "forall i : C ." +
     "forall j : C ." +
      "(minr(j) * d2(j) - minr(i) * d2(i) + x1(i) - x1(j) )^2 +" + 
      "(minr(i) * d1(i) - minr(j) * d1(j) + x2(i) - x2(j))^2 >=" +
      "(minr(i) + minr(j) + protectedzone())^2")


val inv1 = 
  parseFormula (
    "forall i : C . (  " +
     "(ca(i) = 0 | ca(i) = 1) " +
    " & v(i) * ca(i) = om(i) * minr(i) * ca(i) )"
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


val incatct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      tryruleT(andRight)<(
        easiestT,
        composelistT(
          alphaT*,
          instantiatebyT(St("C"))(List (("i", List("i")))),
          easiestT
        )
      ),
      tryruleT(andRight)<(
        easiestT,
        composelistT(
          alphaT*,
          instantiatebyT(St("C"))(List (("i", List("i")),
                                        ("j", List("i")))),
          hideunivsT(St("C")),
          alphaT*,
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
      )
    )
  )


val outcatct = 
   composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      incatct,
      incatct
    )
)

val controltct = composelistT(hpalphaT*,
                              tryruleT(andRight)<(incatct, outcatct))

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
   tryruleT(diffStrengthen(constinv1))<(
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

val simpcut =
  cutT(DirectedCut,
       parseFormula(" (1 - 0) * X  = (1 - 0) * D"),
       parseFormula("X  = D"))

                   

val postors = nilT

val postconditiontct = 
  composelistT(
    alphaT*,
    hideallbutT(List(LeftP(0), LeftP(1), LeftP(3), RightP(0))),
    cutT(
      DirectedCut,
      parseFormula(
        "forall i:C.forall j:C." +
          "(minr(j) * d2(j) - minr(i) * d2(i) + x1(i) - x1(j))^2 " +
           "+ (minr(i) * d1(i) - minr(j) * d1(j) + x2(i) - x2(j))^2" +
           ">= (minr(i) + minr(j) + protectedzone())^2"),
    parseFormula(
        "forall i:C.forall j:C." +
          "(minr(j) * d2(j) + x1(i) - x1(j))^2 " +
           "+ (- minr(j) * d1(j) + x2(i) - x2(j))^2" +
           ">= ( minr(j) + protectedzone())^2")
    )<(
      composelistT(
        instantiatebyT(St("C"))(List(("i", List("i")),
                                     ("j", List("j")),
                                     ("k", List("i", "j"))))*,
        alphaT*,
        nullarizeT*
      ),
      nilT
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

