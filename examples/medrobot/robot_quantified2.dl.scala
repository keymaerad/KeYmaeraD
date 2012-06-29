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
     "((ZZ = first()) | " +
     "[w() := first(); {?next(w()) /= ZZ; w() := next(w())}*] " + 
     "((qx() + K() * fx() * g() * s() + 1 / 2 * K() * FXP * g() * s()^2 " + 
     "- px(w())) * nx(w()) + " + 
     " (qy() + K() * fy() * g() * s() + 1 / 2 * K() * FYP * g() * s()^2 " +
     "- py(w())) * ny(w()) >= 0))")

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



val main =
   // outer loop
   tryruleT(loopInduction(loopInvOuter))<(
     // outer loop base case
     composelistT(
        hpalphaT*,
      	tryruleT(andRight)<(
      	   easiestT,
      	   composelistT(
      	      hpalphaT*,
      	      tryruleatT(reorder)(LeftP(7)),
      	      tryruleatT(reorder)(LeftP(7)),

      	      unifyT(parseFormula("ZZ = first()"), loopInvSimple,
      	         (x => tryruleT(loopInduction(x))))<(
      	      	 tryruleT(andRight)<(
      	      	   easiestT,
      	      	   composelistT(
      	      	      tryruleT(iterate),
      	      	      hpalphaT*,
		      tryruleT(impLeft)<(
		        tryruleT(andRight)<(
			easiestT,
			composelistT(
			  tryruleT(impRight),
			  hpalphaT*,
			  tryruleT(iterate),
			  hpalphaT*,
			  tryruleatT(hide)(LeftP(10)),
			  substT*,
			  easiestT)),
			easiestT),
		      nilT)),
      	      	 composelistT(
      	      	   hpalphaT*,
      	      	   easiestT
      	      	   // tryruleT(andRight)<(
      	      	   //    nilT,
      	      	   //    nilT)
      	      	      ),
      	      	 easiestT),


      	      nilT)))
	      ,
     // outer loop inductive step
        nilT
     // composelistT(
     //    hpalpha1T*,
     // 	tryruleatT(reorder)(LeftP(7)),
     //    newestT("fyp",
     //       fyp_string =>
     //          newestT("fxp",
     //             fxp_string =>
     // 	            unifyT(parseFormula("ZZ = first()"),
     //                   Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
     // 	                  Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
     // 	                     loopInvInner)),
     // 	               (x => tryruleT(loopInduction(x))))))<(
     //       composelistT(easiestT),
     // 	   nilT,	  
     //       composelistT(
     // 	      hpalphaT*,
     //          diffsolveT(RightP(0), Endpoint),
     //          hpalphaT*,
     //          substT*,
     // 	      hpalphaT*)))
	      ,
     // outer loop invariant implies precondition
     nilT
//     composelistT(easiestT)
     )


}

