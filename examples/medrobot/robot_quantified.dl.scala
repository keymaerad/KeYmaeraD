object Script {

// this is the proof script for robot_quantified.dl
// a theorem about the safety of the control algorithm that enforces a
// multiple virtual fixtures in 2D, with force feedback


val loopInvOuter =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
              "(forall r : B. nx(r)^2 + ny(r)^2 = 1) & " +
	      "(forall i : B. <j() := first(); {?(j() /= end()); j() := next(j())}* >(i=j())) & " +
              "(forall z : B. (w(z) = 1) ==> (z /= end())) & " +
              "(forall z : B. (z /= end()) ==> (w(z) = 1)) & " +
	      "(forall m : B. (m /= end()) ==> " +
	      "(qx() - px(m)) * nx(m) + (qy() - py(m)) * ny(m) >= 0)")

val loopInvInner =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
              "(forall r : B. nx(r)^2 + ny(r)^2 = 1) & " +
	      "(forall i : B. <j() := first(); {?(j() /= end()); j() := next(j())}* >(i=j())) & " +
              "(forall z : B. (W = 1) ==> (z /= end())) & " +
	      "(forall m : B. (m /= end()) ==> (qx() - px(m)) * nx(m) + (qy() - py(m)) * ny(m) >= 0) & " +
              "(forall z : B. ((W = 1) ==> " + 
	      "((qx() + K() * fx() * g() * s() + 1 / 2 * K() * FXP * g() * s()^2 " + 
	      "- px(z)) * nx(z) + " + 
	      " (qy() + K() * fy() * g() * s() + 1 / 2 * K() * FYP * g() * s()^2 " +
	      "- py(z)) * ny(z) >= 0)))")


val main =
   // outer loop
    tryruleT(loopInduction(loopInvOuter))<(
     tryruleT(andRight)<(
	  easiestT,
	  composelistT(
	    hpalphaT*,
            instantiatebyT(St("B"))(List (("z", List("m")), ("m", List("m")))),
	    nullarizeT*,
	    easiestT)),
     composelistT(
        hpalphaT*,
        tryruleatT(reorder)(LeftP(6)),
        newestT("w",
           w_string =>
        newestT("fyp",
           fyp_string =>
              newestT("fxp",
                 fxp_string =>
                    unifyT(parseFormula("ZZ = first()"),
                       Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
	                  Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
	                    Prover.extract(Var("W"), loopInvInner)
			        (Fn(w_string, List(Var("z")))))),
	               (x => tryruleT(loopInduction(x)))))))<(
			      composelistT(easiestT,
			         instantiatebyT(St("B"))(List (("z", List("z")))),
			         nullarizeT*,
				 hidethencloseT),
			     tryruleT(andRight)<(easiestT,nilT),
			     nilT),


	nilT),
      composelistT(
            hpalphaT*,
            instantiatebyT(St("B"))(List (("z", List("v")), ("m", List("v")))),
	    nullarizeT*,
	    easiestT))



}

