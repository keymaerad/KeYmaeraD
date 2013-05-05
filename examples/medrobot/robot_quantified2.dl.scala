object Script {

// this is the proof script for robot_quantified2.dl
// a theorem about the safety of the control algorithm that enforces a
// multiple virtual fixtures in 2D, with force feedback


val loopInvOuter =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
              "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
	      "(first() /= next(last())) & " +
	      "[m() := first(); {?m() /= last(); m() := next(m())}*] " + 
	      "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) >= 0)")

 val loopInvInner =
  parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
     "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
     "(first() /= next(last())) & " +
     "[m() := first(); {?m() /= last(); m() := next(m())}*] " + 
     "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) >= 0) &" +
     "((ZZ /= first()) ==> " +
     "[w() := first(); {?next(w()) /= ZZ; w() := next(w())}*] " + 
     "((qx() + K() * fx() * g() * s() + 1 / 2 * K() * FXP * g() * s()^2 " + 
     "- px(w())) * nx(w()) + " + 
     " (qy() + K() * fy() * g() * s() + 1 / 2 * K() * FYP * g() * s()^2 " +
     "- py(w())) * ny(w()) >= 0))")


val loopInvInnerInner = 
    parseFormula(
"(QXX = qx() + K() * fx() * g() * s() + 1/2 * K() * FXXP * g() * s()^2) &"+
"(QYY = qy() + K() * fy() * g() * s() + 1/2 * K() * FYYP * g() * s()^2) &"+
"(FXX = fx() + FXXP * s()) &" +
"(FYY = fy() + FYYP * s()) &" +
"[w() := ZZ; {?w() /= last();  w() := next(w())}*]" +
"(qx() + K() * fx() * g() * s() + 1 / 2 * K() * FXXP * g() * s()^2 - px(w())) * nx(w()) + " +
"(qy() + K() * fy() * g() * s() + 1 / 2 * K() * FYYP * g() * s()^2 - py(w())) * ny(w()) >= 0")



// safe(i) /\ i /= last -> safe(next(i))

// val loopInvSimple =
//  parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
//               "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
// 	      "(first() /= next(last())) & " +
// 	      "[m() := ZZ; {?m() /= last(); m() := next(m())}*] " + 
// 	      "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) >= 0)")


val loopInvSimple =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
    "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
    "(first() /= next(last())) & " +
    "(((qx() - px(ZZ)) * nx(ZZ) + (qy() - py(ZZ)) * ny(ZZ) >= 0) & " +
    "(ZZ /= last() ==> ((qx() - px(next(ZZ))) * nx(next(ZZ)) + " + 
    "(qy() - py(next(ZZ))) * ny(next(ZZ)) >= 0)))")





val easybranchT : Tactic => Tactic = 
    foo => 
  composelistT(
    hpalpha1T*,
    diffsolveT(RightP(0), Endpoint),
    hpalpha1T*,
      tryruleT(andRight)<(
      easiestT,
      composelistT(
        substT*,
        foo)))

val safeproof = 
     (b1 : Tactic, b2 : Tactic, b3 : Tactic, b4 : Tactic, b5 : Tactic, b6 : Tactic, b7 : Tactic) =>
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
                             easybranchT(b1),
                             // branch 2
			     easybranchT(b2))),
                         //branch 3
                         easybranchT(b3))),
                     // branch 4
                     easybranchT(b4))),
                 // branch 5
                 easybranchT(b5))),
             // branch 6
	     easybranchT(b6))),
       	// branch 7
        easybranchT(b7)))


// branchpf(
//   List( // list of formulas to help bind temporary variables
//     parseFormula(
//       ...)),
//   parseFormula( // cut, that uses these bindings
//     ...),
//   composelistT( // preparatory unsubstitutions to arithT
//     unsubT(
//       parseFormula( // logic variables bound to terms through unification
//         ...),
//       List(...)))) // list of temp variables to unsubstitute

val rearrangepf = 
             composelistT(
               tryruleatT(hide)(LeftP(9)),
               tryruleatT(hide)(LeftP(8)),
               tryruleatT(hide)(LeftP(7)),
               tryruleatT(hide)(LeftP(6)),
               tryruleatT(hide)(LeftP(5)),
               tryruleatT(hide)(LeftP(4)),
               tryruleatT(hide)(LeftP(3)),
               tryruleatT(hide)(LeftP(2)),
               tryruleatT(hide)(LeftP(1)),
               arithT
             )


val branchpf = 
    (matchlist : List[Formula], cutformula : Formula, unsubst : Tactic) =>
    cutmT(StandardCut,matchlist,cutformula)<(
      composelistT(unsubst,arithT),
      rearrangepf)


val safeproofu1 =
    safeproof(nilT,nilT,nilT,nilT,nilT,nilT,nilT)

       // branchpf( // branch 1
       //   List(
       //     parseFormula(
       //       "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() + " +
       //       "K() * 1 * ((fx() * nx() + fy() * ny() + fz() * nz()) * e() + " +
       //       "(FXP * nx() + FYP * ny() + FZP * nz()) * e()^2 * (1 / 2)) >= 0")),
       //   parseFormula(
       //     "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //     "1 * " +
       //     "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //     "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //   composelistT(
       //     unsubT(
       //       parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
       //       List(Var("FN"),Var("FNP"),Var("D0"))))),

       //  branchpf( // branch 2
       //    List(
       //      parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny() + FZP * nz()) * e()^2) = 1")),
       //    parseFormula(
       //      "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       // 	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz()) * TMP) * " +
       // 	    "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       // 	    "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //    composelistT(
       //      unsubT(
       //        parseFormula(
       //          "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
       //          List(Var("FN"),Var("FNP"),Var("D0"))))),

       //  branchpf(  // branch 3
       //    List(
       //      parseFormula("FXP * nx() + FYP * ny() + FZP * nz() >= 0")),
       //    parseFormula(
       //      "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //      "1 * " +
       //      "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //      "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //    composelistT(
       //      unsubT(
       //        parseFormula(
       //          "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 <= 0"),
       //        List(Var("FNP"),Var("FN"),Var("D0"))))),

       //  branchpf( // branch 4
       //    List(
       //      parseFormula("TMP * K() * A = 1"),
       //      parseFormula("fx() * nx() + fy() * ny() + fz() * nz() + (FXP * nx() + FYP * ny() + FZP * nz()) * e() >= 0")),
       //    parseFormula(
       //      "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //      "(2 * (FXP * nx() + FYP * ny() + FZP * nz()) * " +
       //      "((qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz()) * TMP) * " +
       //      "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //      "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //    composelistT(
       //      unsubT(
       //        parseFormula(
       //          "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 >= 0"),
       //        List(Var("FN"),Var("FNP"),Var("D0"))))),


       // branchpf( // branch 5
       //   List(
       //     parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny() + FZP * nz()) * e()^2) = 1")),
       //   parseFormula(
       //     "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //     "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz()) * TMP) * " +
       //     "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //     "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //   composelistT(
       //     unsubT(
       //       parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
       //       List(Var("FNP"),Var("FN"),Var("D0"))))),


       // branchpf( // branch 6
       //   List(
       //     parseFormula("FXP * nx() + FYP * ny() + FZP * nz() >= 0")),
       //   parseFormula(
       //     "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //     "1 * " +
       //     "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //     "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //   composelistT(
       //     unsubT(
       //       parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
       //       List(Var("FNP"),Var("FN"),Var("D0"))))),


       // branchpf( // branch 7
       //   List(
       //     parseFormula("FXP * nx() + FYP * ny() + FZP * nz() >= 0")),
       //   parseFormula(
       //     "(qx() - px()) * nx() + (qy() - py()) * ny() + (qz() - pz()) * nz() +" +
       //     "1 * " +
       //     "(K() * (fx() * nx() + fy() * ny() + fz() * nz()) * s() + " +
       //     "(1 / 2) * K() * (FXP * nx() + FYP * ny() + FZP * nz()) * s()^2) >= 0 "),
       //   composelistT(
       //     unsubT(
       //       parseFormula("FNP >= 0"),
       //       List(Var("FNP"))),
       //     unsubT(
       //       parseFormula("D0 >= 0"),
       //       List(Var("D0"))))))

val singleboundarypf =
     composelistT(
       hpalpha1T*,
       tryruleT(andRight)<(
         composelistT(
       	   hpalpha1T*,
       	   tryruleT(andRight)<(
             safeproofu1
,
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
                                       hpalpha1T*,
                                       tryruleT(andRight)<(
nilT//                                         safeproofu1
,
nilT//                                         safeproofu1
)),
nilT//                                     safeproofub
)),
nilT//			         safeproofuc
)),
nilT//			     safeproofud
)),
nilT//			 safeproofu1
)),
nilT//		     safeproofu1b
)),
nilT//		 safeproofu
)))),
nilT//	 safeproofu0
))



val main =
   // outer loop
   tryruleT(loopInduction(loopInvOuter))<(
     // outer loop base case
     tryruleT(andRight)<(
       easiestT,
       composelistT(
         tryruleT(seq)*,
         tryruleatT(renameAssign("ii"))(LeftP(5)),
         tryruleatT(renameAssign("ii"))(RightP(0)),
	 nonarithcloseT
       )
     ),
     composelistT(
        tryruleT(andLeft)*,
        tryruleT(seq)*,
        tryruleT(assignAnyRight)*,
        tryruleatT(assign)(RightP(0)),
      	tryruleatT(reorder)(LeftP(6)),
        newestT("fyp",
           fyp_string =>
              newestT("fxp",
                 fxp_string =>
      	           unifyT(parseFormula("ZZ = first()"),
                       Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
      	                 Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
      	                    loopInvInner)),
      	              (x => tryruleT(loopInduction(x))))))<(
          // inner loop base case
          tryruleT(andRight)<(
	    tryruleT(andRight)<(
	      easiestT,
	      composelistT(
	        tryruleT(seq)*,
		easiestT
	      )
	    ),
	    composelistT(
	      tryruleT(impRight),
              tryruleatT(hide)(LeftP(7)),
              cutT(StandardCut,parseFormula("ZZ=first()"),
	           parseFormula("first()/=first()"))<(
	        composelistT(substT*,easiestT),easiestT)
	    )
	  ),
          // inner loop inductive step
          nilT, //           singleboundarypf,
          // inner loop postcondition
          composelistT(
	     hpalphaT*,
             diffsolveT(RightP(0), Endpoint),
	     tryruleT(impLeft)<(
	        composelistT(
		  tryruleatT(assign)(RightP(0)),
		  tryruleatT(assign)(LeftP(0)),
		  tryruleT(andRight)<(
		     easiestT,
		     composelistT(
		        tryruleatT(hide)(LeftP(20)),
		        tryruleatT(hide)(LeftP(19)),
		        tryruleatT(hide)(LeftP(18)),
		        tryruleatT(hide)(LeftP(17)),
		        tryruleatT(hide)(LeftP(10)),
		        tryruleatT(hide)(LeftP(8)),
/////////
	                tryruleatT(seq)(RightP(0)),
	                tryruleatT(assign)(RightP(0)),
			
// 
//  


        newestT("fyp",
           fyp_string =>
              newestT("fxp",
                 fxp_string =>
unifyT(parseFormula("FYY = fy() + DD * s()"),
       Prover.substitute_Formula("FYYP", Fn(fyp_string, Nil),
           Prover.substitute_Formula("FXXP", Fn(fxp_string, Nil),
               loopInvInnerInner)),
       (v => unifyT(parseFormula("FXX = fx() + CC * s()"), v,
          (w => unifyT(parseFormula("QYY = qy() + K() * fy() * g() * s() + 1 / 2 * K() * BB * g() * s()^2"), w,
             (z => unifyT(parseFormula("QXX = qx() + K() * fx() * g() * s() + 1 / 2 * K() * AA * g() * s()^2"), z,
                (y => unifyT(parseFormula("ZZ = first()"), y,
                   (x => tryruleT(loopInduction(x))))))))))))))<(
          composelistT(
	    tryruleT(andRight)<(easiestT,
	       composelistT(
	         tryruleatT(hide)(LeftP(15)),
	         tryruleatT(hide)(LeftP(14)),
	         tryruleatT(hide)(LeftP(13)),
	         tryruleatT(hide)(LeftP(12)),
	         tryruleatT(hide)(LeftP(11)),
	         tryruleatT(hide)(LeftP(10)),
	         tryruleatT(hide)(LeftP(9)),

	         tryruleatT(hide)(LeftP(6)),
	         tryruleatT(hide)(LeftP(5)),
	         tryruleatT(hide)(LeftP(4)),
	         tryruleatT(hide)(LeftP(3)),
	         tryruleatT(hide)(LeftP(1)),
	         tryruleatT(hide)(LeftP(0)),

	         nilT
	       )
	    )
	  ),
	  composelistT(
	    tryruleatT(seq)(RightP(0))*,
	    tryruleatT(check)(RightP(0)),
	    tryruleT(impRight),
	    tryruleT(assign)*,
	    tryruleT(andLeft)*,
	    tryruleT(andRight)<(
	      easiestT,
	      composelistT(
      	         tryruleatT(hide)(LeftP(4)),
	         tryruleatT(hide)(LeftP(3)),
	         tryruleatT(hide)(LeftP(2)),
	         tryruleatT(hide)(LeftP(1)),
		 tryruleT(seq)*,
		 tryruleatT(assign)(LeftP(1)),
		 tryruleatT(iterate)(LeftP(1)),
		 tryruleT(andLeft)*,
		 tryruleT(seq)*,
	         tryruleatT(hide)(LeftP(1)),
		 tryruleatT(check)(LeftP(1)),
		 tryruleT(impLeft)<(
		   composelistT(
		     tryruleatT(renameAssign("ii"))(LeftP(1)),
		     tryruleatT(renameAssign("ii"))(RightP(0)),
		     nilT //
		   ),
		   composelistT(
		     tryruleatT(hide)(RightP(1)),
		     substT*,
		     nonarithcloseT
		   )
		 ),
		 nilT
	      )
	    ),
	    nilT
	  ),
	  composelistT(
	    hpalphaT*,
	    tryruleT(iterate),
	    tryruleT(andLeft)*,
            tryruleatT(hide)(LeftP(5)),
	    substT*,
	    easiestT
	  )
       ),
/////////
		        nilT
		     )
		  ),
		  nilT
		),
		composelistT(
		  tryruleatT(hide)(RightP(1)),
		  tryruleatT(hide)(LeftP(8)),
		  tryruleatT(hide)(LeftP(6)),
		  tryruleatT(hide)(LeftP(5)),
		  tryruleatT(hide)(LeftP(4)),
		  tryruleatT(hide)(LeftP(3)),
		  tryruleatT(hide)(LeftP(1)),
		  tryruleatT(hide)(LeftP(0)),
		  substT*,
		  commuteequalsT,
		  nonarithcloseT
		)
 	     ),
	     nilT
	  )
       )
     ),
     // outer loop invariant implies postcondition
     composelistT(
       tryruleT(andLeft)*,
       tryruleT(seq)*,
       tryruleatT(renameAssign("ii"))(LeftP(5)),
       tryruleatT(renameAssign("ii"))(RightP(0)),
       nonarithcloseT
     )
   )


}

