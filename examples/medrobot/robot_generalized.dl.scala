object Script {

val loopInv =
 parseFormula("K() > 0 & e() > 0 & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")


val cut2 = 
  cutT(
    StandardCut,
    parseFormula(
       "G = FN + (D0 + 1 / 2 * K * FNP * e()^2) * TMP"),
    parseFormula(
       "((1/2) * K * FNP < 0 )  ==>" + 
       "((forall x1 . forall x2 . ( FN < - FNP * x1 & x1 < x2) ==> "+
       " (1/2) * K * FNP * x1^2 + K * FN * x1 > " +
       " (1/2) * K * FNP * x2^2 + K * FN * x2 )  & " +
       " (forall x1 . forall x2 . (FN > - FNP * x1 & x1 > x2) ==> "+
       " (1/2) * K * FNP * x1^2 + K * FN * x1 > " +
       " (1/2) * K * FNP * x2^2 + K * FN * x2 )  ) "
    )
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
                             composelistT(
                               hpalpha1T*
                             ),
                             // working here
                             composelistT(
                               hpalpha1T*,
                               diffsolveT(RightP(0), Endpoint),
                               hpalpha1T*,
                               tryruleT(andRight)<(
                                 easiestT,
                                 cut2<(
                                   alleasyT,
                                   nilT
                                 )
                               )
                             )
                           )
                         ),
                         composelistT(
                           hpalpha1T*
                         )
                       )
                     ),
                     composelistT(
                       hpalpha1T*
                     )
                   )
                 ),
                 composelistT(
                   hpalpha1T*
                 )
               )
             ),
             composelistT(
               hpalpha1T*
             )
           )
         ),
         composelistT(
           hpalpha1T*
         )
       )
     ),
     easiestT
   )

}
