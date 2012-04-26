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
                   )
                 ),

		 // branch 5
                  composelistT(
	        	   hpalpha1T*,
	        	   tryruleT(andRight)<(
	        	    composelistT(hpalpha1T*,
	        	                 tryruleT(andRight)<(
	        			 composelistT(hpalpha1T*,
                                              diffsolveT(RightP(0), Endpoint),
	        			      hpalpha1T*,
	        			      tryruleT(andRight)<(
                                                  easiestT,
	        			          composelistT(
						             substT*, 
	        			                     tryruleatT(hide)(LeftP(14)),
	        			                     tryruleatT(hide)(LeftP(12)),
	        			                     tryruleatT(hide)(LeftP(10)),
	        			                     tryruleatT(hide)(LeftP(6)),
	        			                     tryruleatT(hide)(LeftP(2)),
	        			                     tryruleatT(hide)(LeftP(0)),
	        			                     arithT
	        			          )
                                             )
                                         ),
	        			 composelistT(hpalpha1T*,
                                              diffsolveT(RightP(0), Endpoint),
				              hpalpha1T*,
					      tryruleT(andRight)<(
                                                  easiestT,
						  composelistT(
						             substT*,
	        			                     tryruleatT(hide)(LeftP(9)),
	        			                     tryruleatT(hide)(LeftP(8)),
							     cutb5a<(composelistT(
     								     tryruleatT(hide)(LeftP(6)),
								     unsubT(parseFormula(
								     "FN <= 0"),
							              List(Var("FN"))),
								      unsubT(parseFormula(
								      "Q + K() * (A * e() + FNP * e()^2 * (1 / 2)) <= 0"),
								      List(Var("Q"),Var("FNP"))),
								      arithT),
	        			                             composelistT(
								     tryruleatT(hide)(LeftP(11)),
								     tryruleatT(hide)(LeftP(10)),
								     tryruleatT(hide)(LeftP(9)),
	        			                             tryruleatT(hide)(LeftP(8)),
	        			                             tryruleatT(hide)(LeftP(7)),
	        			                             tryruleatT(hide)(LeftP(6)),
	        			                             tryruleatT(hide)(LeftP(5)),
	        			                             tryruleatT(hide)(LeftP(4)),
	        			                             tryruleatT(hide)(LeftP(3)),
	        			                             tryruleatT(hide)(LeftP(2)),
	        			                             tryruleatT(hide)(LeftP(1)),
							             arithT))

                                                  )
                                              )
                                         )
                                       ), nilT),
                      composelistT(hpalpha1T*,
		                diffsolveT(RightP(0), Endpoint), 
                                hpalpha1T*,
                                tryruleT(andRight)<(
                                  easiestT,
                                  composelistT(substT*,arithT))
                               )))
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
