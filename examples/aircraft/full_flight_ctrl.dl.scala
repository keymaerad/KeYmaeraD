object Script {


val maininv = 
  parseFormula (
   "((forall i : C ." +
         "forall j : C ."+
            "(disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2 >= (4*minr() + protectedzone())^2) "+
      "& (forall i : C . (c1(i) -x1(i))^2 + (c2(i) - x2(i))^2 = minr()^2)" +
      "& (forall i : C . (c1(i) - disc1(i))^2 + (c2(i) - disc2(i))^2 = minr()^2))")

val inv1 = 
  parseFormula (
   "forall i : C . " +
   "(ca(i) = 1 & d1(i) = -om(i) * (x2(i) - c2(i)) & "+
   " d2(i) = om(i) * (x1(i) - c1(i)) & " +
   "discom(i) = 0 & ddisc1(i) = 0 & ddisc2(i) = 0"+
    ") | (" +
    " ca(i) = 0 & x1(i) = disc1(i) & x2(i) = disc2(i) & d1(i) = ddisc1(i) & d2(i) = ddisc2(i)" +
   " & om(i) = discom(i))"
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

val evolvetct = nilT

val indtct =
  composelistT(hpalphaT*,
               tryruleT(andRight)<(controltct, evolvetct))

val starttct =
   tryruleT(loopInduction(Binop(And,maininv, inv1)))<(
     easiestT,
     indtct,
     easiestT)

val main = starttct

}
