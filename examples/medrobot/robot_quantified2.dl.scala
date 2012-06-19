object Script {

// this is the proof script for robot_quantified2.dl
// a theorem about the safety of the control algorithm that enforces a
// multiple virtual fixtures in 2D, with force feedback


val loopInv =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
              "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
	      "[j() := first(); {?j() /= last(); j() := next(j())}*] " + 
	      "((qx() - px(j())) * nx(j()) + (qy() - py(j())) * ny(j()) >= 0)")

val loopInv2 =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
    "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
    "[j() := first(); {?j() /= ZZ; j() := next(j())}*] " + 
    "((qx() " + 
    "- px(j())) * nx(j()) + " + 
    " (qy() " +
    "- py(j())) * ny(j()) >= 0)")


 val loopInv3 =
  parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
     "(forall i : B. nx(i)^2 + ny(i)^2 = 1) & " +
     "[j() := first(); {?j() /= ZZ; j() := next(j())}*] " + 
     "((qx() + K() * fx() * g() * s() + 1 / 2 * K() * FXP * g() * s()^2 " + 
     "- px(j())) * nx(j()) + " + 
     " (qy() + K() * fy() * g() * s() + 1 / 2 * K() * FYP * g() * s()^2 " +
     "- py(j())) * ny(j()) >= 0)")




val main =
   tryruleT(loopInduction(loopInv))<(
     composelistT(easiestT),
     composelistT(
        hpalphaT*,
	tryruleatT(reorder)(LeftP(6)),
        newestT("fyp",
        fyp_string =>
        newestT("fxp",
        fxp_string =>
	unifyT(parseFormula("ZZ = first()"),
		Prover.substitute_Formula("FYP",
					  Fn(fyp_string, Nil),
					  Prover.substitute_Formula("FXP", Fn(fxp_string, Nil), loopInv3)),
	       (x => tryruleT(loopInduction(x))))))<(
          composelistT(easiestT),
	  nilT,	  
          composelistT(
	   hpalpha1T*,
           diffsolveT(RightP(0), Endpoint),
           hpalpha1T*,
           substT*))),
     composelistT(easiestT))
}

