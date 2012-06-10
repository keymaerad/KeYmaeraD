object Script {

// this is a proof script for robot_generalized2.dl
// a theorem about the safety of the control algorithm that enforces a
// single virtual fixture in 2D, without force feedback

val loopInv =
 parseFormula("K() > 0 & e() > 0 & g <= 1 & g >= 0  & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")


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

val cutb2 = 
  cutT(
    StandardCut,
    parseFormula("TMP * K() * (A * e() + "+ 
      "1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1"),
    parseFormula(
       "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
       "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
       "(K() * (fx() * nx() + fy() * ny()) * s() + " +
       "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 ")
  )



val cutb5a = 
  cutmT(
    StandardCut,
    List(parseFormula("TMP * K() * e() = 1"),
         parseFormula("FXP * nx() + FYP * ny() > 0")),
    parseFormula("((qx() - px()) * nx() + (qy() - py()) * ny()) + " +
                 "(K() * ((fx() * nx() + fy() * ny()) - " +
		 "((fx() * nx() + fy() * ny()) + ((qx() - px()) * nx() + " +
		 "(qy() - py()) * ny() + 1 / 2 * K() * (FXP * nx() + FYP * " +
		 "ny()) * e()^2) * TMP)) * s()) " +
		 "+ 1 / 2 * K() * (FXP * nx() + FYP * ny())* s()^2 >= 0"))





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
                             // branch 1
                             easybranchT,

                             // branch 2
                             composelistT(
                               hpalpha1T*,
                               diffsolveT(RightP(0), Endpoint),
                               hpalpha1T*,
                               tryruleT(andRight)<(
                                 easiestT,
                                 composelistT(
                                   substT*,
                                   cutb2<(
                                     arithT,
                                     arithT
                                   )
                                 )
                               )
                             )
                           )
                         ),
                         //branch 3
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
                     // branch 4
                     easybranchT
		     // composelistT(
                     //     hpalpha1T*,
                     // 	 diffsolveT(RightP(0), Endpoint),
                     //     hpalpha1T*,
                     //     tryruleT(andRight)<(
                     //       easiestT,
                     //       composelistT(
                     //         substT*,
		     // 	     cutb2<( // using the same cut as branch 2..
                     //           arithT,
                     //           arithT
                     //         )
                     //       )
                     //     )
                     // )
                   )
                 ),

		 // branch 5
		     composelistT(
                         hpalpha1T*,
                     	 diffsolveT(RightP(0), Endpoint),
                         hpalpha1T*,
                         tryruleT(andRight)<(
                           easiestT,
                           composelistT(
                             substT*,
			     cutb2<( // using the same cut as branch 2..
                               arithT,
                               arithT
                             )
                           )
                         )
                     )
              )
             ),
             // branch 6
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
	 // branch 7
         easybranchT
       )
     ),
     easiestT
   )
}
