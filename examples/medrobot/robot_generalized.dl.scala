object Script {

val loopInv =
 parseFormula("K() > 0 & e() > 0 & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")


val easybranchT = 
  composelistT(
    hpalphaT*,
    diffsolveT(RightP(0), Endpoint),
    hpalphaT*,
      tryruleT(andRight)<(
      easiestT,
      alleasyT
    )
  )

val cutb2 = 
  cutT(
    StandardCut,
    parseFormula(
      "(qx() + K() * (fx() - (fx() * nx() + fy() * ny() + " + 
      "((qx() - px()) * nx() + (qy() - py()) * ny() + " +
      "1 / 2 * K() * (FXP * nx() + FYP * ny()) * e()^2) * TMP) * nx()) * s() + " +
      "1 / 2 * K() * FXP * s()^2 - px()) * nx() + " +
      "(qy() + K() * (fy() - (fx() * nx() + fy() * ny() + " +
      "((qx() - px()) * nx() + (qy() - py()) * ny() + " +
      "1 / 2 * K() * (FXP * nx() + FYP * ny()) * e()^2) * TMP) * ny()) * s() + " +
      "1 / 2 * K() * FYP * s()^2 - py()) * ny() >= 0"),
    parseFormula(
      "((qx() - px() ) + K() * (fx() - (fx() * nx() + fy() * ny() + " + 
      "((qx() - px()) * nx() + (qy() - py()) * ny() + " +
      "1 / 2 * K() * (FXP * nx() + FYP * ny()) * e()^2) * TMP) * nx()) * s() + " +
      "1 / 2 * K() * FXP * s()^2) * nx() + " +
      "((qy() - py()) + K() * (fy() - (fx() * nx() + fy() * ny() + " +
      "((qx() - px()) * nx() + (qy() - py()) * ny() + " +
      "1 / 2 * K() * (FXP * nx() + FYP * ny()) * e()^2) * TMP) * ny()) * s() + " +
      "1 / 2 * K() * FYP * s()^2) * ny() >= 0")
  )



val cutb5 = 
  cutT(
    StandardCut,
    parseFormula("TMP * TMP * K() = 2 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * (FXP * nx() + FYP * ny())"),
    parseFormula("((qx() - px()) + K() * (fx() - (fx() * nx() + fy() * ny() - TMP) * nx()) * e() + " +
                 "1 / 2 * K() * FXP * e()^2) * nx() + " +
                 "((qy() - py()) + K() * (fy() - (fx() * nx() + fy() * ny() - TMP) * ny()) * e() + " + 
                 "1 / 2 * K() * FYP * e()^2) * ny() >= 0"
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
       hpalphaT*,
       tryruleT(andRight)<(
         composelistT(
           hpalphaT*,
           tryruleT(andRight)<(
             composelistT(
               hpalphaT*,
               tryruleT(andRight)<(
                 composelistT(
                   hpalphaT*,
                   tryruleT(andRight)<(
                     composelistT(
                       hpalphaT*,
                       tryruleT(andRight)<(
                         composelistT(
                           hpalphaT*,
                           tryruleT(andRight)<(
                             // branch 1
                             easybranchT,
                             // branch 2
                             composelistT(
                               hpalphaT*,
                               diffsolveT(RightP(0), Endpoint),
                               hpalphaT*,
                               tryruleT(andRight)<(
                                 easiestT,
                                 composelistT(
                                   substT*,
                                   cutb2<(
                                     composelistT(
                                       tryruleT(unsubstitute(Fn("-", List(Fn("qx", Nil), Fn("px", Nil))))),
                                       tryruleT(unsubstitute(Fn("-", List(Fn("qy", Nil), Fn("py", Nil))))),
                                       arithT
                                     ),
                                     arithT
                                   )
                                 )
                               )
                             )
                           )
                         ),
                         //branch 3
                         composelistT(
                           hpalphaT*,
                           diffsolveT(RightP(0), Endpoint),
                           hpalphaT*,
                           tryruleT(andRight)<(
                             easiestT,
                             hidehasfnT("e")& alleasyT
                           )
                         )
                       )
                     ),
                     // branch 4
                     easybranchT
                   )
                 ),
                 // branch 5
                 composelistT(
                   hpalphaT*,
                   diffsolveT(RightP(0), Endpoint),
                   hpalphaT*,
                   tryruleT(andRight)<(
                     easiestT,
                     composelistT(
                       substT*,
                       cutb5<(
                         composelistT(
                           hidehasfnT("s")*,
                           unsubT(
                             parseFormula(
                               "TMPK = 2 * (X * nx() + Y * ny()) * (FXP * nx() + FYP * ny())"
                             ),
                             List(Var("X"), Var("Y"))
                           ),
                           tryruleatT(hide)(LeftP(6)),
                           arithT

                         ),
                         composelistT(
                           tryruleatT(hide)(LeftP(7)),
                           tryruleatT(hide)(LeftP(8)),
                           tryruleatT(hide)(LeftP(3)),
                           arithT
                         )
                       )
                     )
                   )
                 )

               )
             ),
             // branch 6
             composelistT(
               hpalphaT*,
               diffsolveT(RightP(0), Endpoint),
               hpalphaT*,
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
