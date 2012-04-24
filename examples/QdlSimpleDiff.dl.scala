object Script {
val main = 
  composelistT(
    trylistofrulesT(List(qDiffSolve(Endpoint)(List(parseFormula("forall t . x(t, k) = -(1/2) *b * t^2 + v(k) * t + x(k)"))))),
    hpalphaT*,
    instantiatebyT(St("C"))(List(("i", List("i")),
                                 ("j", List("j")),
                                 ("k", List("i", "j"))))*,
    (nonarithcloseT | alphaT | betaT | nullarizeT | hidethencloseT)*
  )

}
