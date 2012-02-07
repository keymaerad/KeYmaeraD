object Script {


val maininv = 
  parseFormula (
   "forall i : C ." +
         "forall j : C ."+
            "(disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2 >= (4*minr() + protectedzone())^2")


val inv1 = 
  parseFormula (
   "forall k : C . " +
   "(ca(k) = 1 & d1(k) = -om(k) * (x2(k) - c2(k)) & "+
   " d2(k) = om(k) * (x1(k) - c1(k)) & " +
   "discom(k) = 0 & ddisc1(k) = 0 & ddisc2(k) = 0 &"+
   " (c1(k) -x1(k))^2 + (c2(k) - x2(k))^2 = minr()^2 &" +
    "(c1(k) - disc1(k))^2 + (c2(k) - disc2(k))^2 = minr()^2" +
    ") | (" +
    " ca(k) = 0 & x1(k) = disc1(k) & x2(k) = disc2(k) & d1(k) = ddisc1(k) & d2(k) = ddisc2(k)" +
   " & om(k) = discom(k))"
  )

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
    instantiatebyT(St("C"))(List (("i", List("i")),
                                  ("j", List("i")))),
    hideunivsT(St("C")),
    cut1<(
      composelistT(
        alphaT*,
        substT,
        vacuousT*,
        alleasyT
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
      composelistT(
        tryruleT(andRight)<(
          tryruleT(andRight)<(
            tryruleT(close),
            doasgns
          ),
          doasgns
        )
      ),
      doasgns
    )
  )



val exitcatct = 
   composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      easiestT,
      composelistT(
        hpalpha1T*,
        instantiatebyT(St("C"))(List (("i", List("i")),
                                      ("j", List("i")))),
        hideunivsT(St("C")),
        cut1<(
          composelistT(
            alphaT*,
            substT,
            vacuousT*,
            alleasyT
          ),
          composelistT(
            (tryruleT(impLeft) & (tryruleT(close)*))*,
            alleasyT
          )
        )
      )
    )
   )

val controltct = composelistT(hpalphaT*,
                              tryruleT(andRight)<(entercatct, exitcatct))

val evolvetct = 
     tryruleT(diffStrengthen(inv1))<(
       tryruleT(close),
       composelistT(
         alphaT*,
         hideunivsT(St("C")),
         nullarizeT*
       ),
       nilT
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
