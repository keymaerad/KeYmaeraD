object Script {

val loopInv =
 parseFormula("K() > 0 & e() > 0 & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")


val easybranchT = 
  composelistT(
    hpalpha1T*,
    diffsolveT(RightP(0), Endpoint),
    hpalpha1T*,
    tryruleT(andRight)<(
      easiestT,
      alleasyT
    )
  )

val cut2 = 
  cutT(
    StandardCut,
    parseFormula(
       "G = FN + (D0 + 1 / 2 * K * FNP * e()^2) * TMP"),
    parseFormula(
       "((1/2) * K * FNP < 0 )  ==>" + 
       "((forall x1 . forall x2 . (FN - G <= - FNP * x1 & x1 <= x2) ==> "+
      " (1/2) * K * FNP * x1^2 + K * (FN - G) * x1 >= " +
       " (1/2) * K * FNP * x2^2 + K * (FN - G) * x2 )  & "+
       " (forall x1 . forall x2 . (FN - G >= - FNP * x1 & x1 >= x2) ==> "+
       " (1/2) * K * FNP * x1^2 + K * (FN - G) * x1 >= " +
       " (1/2) * K * FNP * x2^2 + K * (FN - G) * x2 ) &  " +
       " ( FN - G <= 0  |   (FN - G >= 0 & ( (FN - G) <= -2 * FNP * s() |  (FN - G) >= -2 * FNP * s()  ) )     ) ) "
    )
  )

val cut2q = 
  cutT(
    StandardCut,
    parseFormula(
       "G = FN + (D0 + 1 / 2 * K * FNP * e()^2) * TMP"),
    parseFormula(
       "forall a : Real. forall  b: Real. " +
       "(a < 0 )  ==>" + 
       "((forall x1 . forall x2 . ( b <= - 2 * a * x1 & x1 <= x2) ==> "+
      " a * x1^2 + b * x1 >= " +
       " a * x2^2 + b * x2 )  & "+
       " (forall x1 . forall x2 . (b >= - 2 * a * x1 & x1 >= x2) ==> "+
       " a * x1^2 + b * x1 >= " +
       " a * x2^2 + b * x2 )  ) "
    )
  )

val cutb6 = 
 cutT(
   StandardCut,
   parseFormula("FXP * nx() + FYP * ny() >= 0"),
   parseFormula("(qx() + K() * (fx() - 0 * nx()) * e() + 1 / 2 * K() * FXP * e()^2 - px()) * nx() + " +
                "(qy() + K() * (fy() - 0 * ny()) * e() + 1 / 2 * K() * FYP * e()^2 - py()) * ny() >= 0")
 )
   




val main =
   tryruleT(loopInduction(loopInv))<(
     easiestT,
     composelistT(
       hpalpha1T*,
       tryruleT(andRight)<(
         composelistT(
           hpalpha1T*,
           tryruleT(andRight)<(
             composelistT(
               hpalpha1T*,
               tryruleT(andRight)<(
                 composelistT(
                   hpalpha1T*,
                   tryruleT(andRight)<(
                     composelistT(
                       hpalpha1T*,
                       tryruleT(andRight)<(
                         composelistT(
                           hpalpha1T*,
                           tryruleT(andRight)<(
                             easybranchT,
                             // working here
                             composelistT(
                               hpalpha1T*,
                               diffsolveT(RightP(0), Endpoint),
                               hpalpha1T*,
                               tryruleT(andRight)<(
                                 easiestT,
                                 nilT,                                 
                                 cutT(
                                   StandardKeepCut,
                                   parseFormula("FNP = FXP * nx() + FYP * ny()"),
                                   parseFormula("~ FNP = 0"))<(
                                     alleasyT,
                                     cut2<(
                                       (hideallbutT(List(LeftP(0), LeftP(4), RightP(0))) & alleasyT),
                                       tryruleT(impLeft)<(
                                         composelistT(
                                           alphaT*,
                                           tryruleatT(allLeft(Fn("s", Nil)))(LeftP(0)),
                                           tryruleatT(allLeft(Fn("e", Nil)))(LeftP(0)),
                                           tryruleatT(allLeft(Fn("s", Nil)))(LeftP(3)),
                                           tryruleatT(allLeft(Num(Exact.Integer(0))))(LeftP(0)),
                                           hideunivsT(Real),
                                           tryruleT(orLeft)<(
                                             composelistT(
                                               tryruleatT(hide)(LeftP(0)),
                                               tryruleT(impLeft)<(
                                                 composelistT(
                                                   nilT
                                                 ),
                                                 easiestT
                                               )
                                             ),
                                             composelistT(
                                               alphaT*,
                                               tryruleT(orLeft)<(
                                                 composelistT(
                                                   tryruleatT(hide)(LeftP(0)),
                                                   tryruleT(impLeft)<(
                                                     nilT,
                                                     easiestT
                                                   )
                                                 ),
                                                 composelistT(
                                                   tryruleatT(hide)(LeftP(1)),
                                                   tryruleT(impLeft)<(
                                                     nilT,
                                                     easiestT
                                                   )
                                                 )
                                               )
                                             )
                                           )
                                         ),
                                         easiestT
                                       )
                                     )
                                   )
                               )
                             )
                           )
                         ),
                         composelistT(
                           hpalpha1T*,
                           diffsolveT(RightP(0), Endpoint),
                           hpalpha1T*,
                           tryruleT(andRight)<(
                             easiestT,
                             hidehasfnT("e")& alleasyT
                           )
                         )
                       )
                     ),
                     easybranchT
                   )
                 ),
                 easybranchT
               )
             ),
             composelistT(
               hpalpha1T*,
               diffsolveT(RightP(0), Endpoint),
               hpalpha1T*,
               tryruleT(andRight)<(
                 easiestT,
                 composelistT(
                   substT*,
                   cutb6<(
                     alleasyT,
                     composelistT(
                       tryruleatT(hide)(LeftP(5)),
                       tryruleatT(hide)(LeftP(6)),
                       arithT
                     )
                   )
                 )
               )
             )
           )
         ),
         easybranchT
       )
     ),
     easiestT
   )

}
