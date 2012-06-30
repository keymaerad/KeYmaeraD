object Script {

  val loopInv =
    Binop(And,
          parseFormula("forall i:C.<j() := first();{?j() /= last(); j() := next(j())}*>i = j()"),
          parseFormula("[k() := first(); {? k() /= J ; k() := next(k())}*; ? k() /= J] x(k()) = 1 ")
        )

  val main =
    composelistT(
      hpalphaT*,
      unifyT(parseFormula("J = first()"),
             loopInv,
             fm => 
               tryruleT(loopInduction(fm))<(
                 nilT,
                 nilT,
                 composelistT(
                   hpalphaT*,
                   instantiatebyselfT(St("C")),
                   hpalphaT*
                 )
               )
           )
    )
}
