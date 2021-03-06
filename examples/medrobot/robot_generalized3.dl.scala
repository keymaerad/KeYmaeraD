object Script {

// this is a proof script for robot_generalized3.dl
// a theorem about the safety of the control algorithm that enforces a
// single virtual fixture in 2D, with force feedback
//
// It has a state variable name that causes trouble (i.e. D), and a
// loop invariant that does not replace the context thrown out by
// the inductive inference rule

val loopInv =
 parseFormula("K() > 0 & e() > 0 & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")


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
        foo
      )
    )
  )



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
			     easybranchT(b2)
                           )
                         ),
                         //branch 3
                         easybranchT(b3)
                       )
                     ),

                     // branch 4
                     easybranchT(b4)
                   )
                 ),
                 // branch 5
                 easybranchT(b5)
              )
             ),
             // branch 6
	     easybranchT(b6)
           )
        ),
       	// branch 7
        easybranchT(b7)
       )
     )


val branchpf = 
    (matchlist : List[Formula], cutformula : Formula, unsubst : Tactic) =>
    cutmT(StandardCut,matchlist,cutformula)<(
      composelistT(unsubst,arithT),
      rearrangepf)


val safeproofud =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * U * ((fx() * nx() + fy() * ny()) * e() + " +
             "(FXP * nx() + FYP * ny()) * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "K() * U * " +
           "((fx() * nx() + fy() * ny()) * s() + " +
           "(FXP * nx() + FYP * ny()) * s()^2 * (1 / 2)) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
       	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
       	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
       	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) <= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "U * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 <= 0"),
              List(Var("FNP"),Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 >= 0"),
              List(Var("FN"),Var("FNP"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0"),
           parseFormula("U * D() = (qx() - px())*nx() + (qy() - py())*ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP < 0"),
             List(Var("FNP"))),
           unsubT(
             parseFormula("U * D() = D0"),
             List(Var("D0"))))))





val safeproofuc =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * U * ((fx() * nx() + fy() * ny()) * e() + " +
             "0 * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * 0 * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
       	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
       	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
       	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * 0 * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) <= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "U * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 <= 0"),
              List(Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 >= 0"),
              List(Var("FN"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * 0 * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * 0 * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) >= 0"),
           parseFormula("0 = FXP * nx() + FYP * ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("0 = FXP * nx() + FYP * ny()"),
           parseFormula("U * D() = (qx() - px())*nx() + (qy() - py())*ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("0 = FNP"), // *
             List(Var("FNP"))),
           unsubT(
             parseFormula("U * D() = D0"),
             List(Var("D0"))))))


val safeproofub =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * U * ((fx() * nx() + fy() * ny()) * e() + " +
             "(FXP * nx() + FYP * ny()) * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
       	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
       	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
       	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) <= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "U * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 <= 0"),
              List(Var("FNP"),Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 >= 0"),
              List(Var("FN"),Var("FNP"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("FXP * nx() + FYP * ny() > 0"),
           parseFormula("U * D() = (qx() - px())*nx() + (qy() - py())*ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP > 0"), // *
             List(Var("FNP"))),
           unsubT(
             parseFormula("U * D() = D0"),
             List(Var("D0"))))))

val safeproofu =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * U * ((fx() * nx() + fy() * ny()) * e() + " +
             "(FXP * nx() + FYP * ny()) * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
       	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
       	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
       	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) <= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "U * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 <= 0"),
              List(Var("FNP"),Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * U * FN)^2 - 2 * K() * U * FNP * D0 >= 0"),
              List(Var("FN"),Var("FNP"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("(K() * U * (fx() * nx() + fy() * ny()))^2 - " +
	                "2 * K() * U * (FXP * nx() + FYP * ny()) * ((qx() - px()) * " +
			"nx() + (qy() - py()) * ny()) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0"),
           parseFormula("U * D() = (qx() - px())*nx() + (qy() - py())*ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "U * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP <= 0"),
             List(Var("FNP"))),
           unsubT(
             parseFormula("U * D() = D0"),
             List(Var("D0"))))))


val safeproofu1b =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * 1 * ((fx() * nx() + fy() * ny()) * e() + " +
             "0 * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * 0 * e()^2) = 1"),
	    parseFormula("0 = (FXP * nx() + FYP * ny())")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("0 = FXP * nx() + FYP * ny()")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "1 * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 <= 0"),
              List(Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 >= 0"),
              List(Var("FN"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * 0 * e()^2) = 1"),
	 parseFormula("0 = (FXP * nx() + FYP * ny())")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("0 = FXP * nx() + FYP * ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("0 = FXP * nx() + FYP * ny()")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP >= 0"),
             List(Var("FNP"))),
           unsubT(
             parseFormula("D0 >= D"),
             List(Var("D0"))))))


val safeproofu1 =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula(
             "(qx() - px()) * nx() + (qy() - py()) * ny() + " +
             "K() * 1 * ((fx() * nx() + fy() * ny()) * e() + " +
             "(FXP * nx() + FYP * ny()) * e()^2 * (1 / 2)) >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf(  // branch 3
          List(
            parseFormula("FXP * nx() + FYP * ny() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "1 * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 <= 0"),
              List(Var("FNP"),Var("FN"),Var("D0"))))),

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * 1 * FN)^2 - 2 * K() * 1 * FNP * D0 >= 0"),
              List(Var("FN"),Var("FNP"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "1 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP >= 0"),
             List(Var("FNP"))),
           unsubT(
             parseFormula("D0 >= 0"),
             List(Var("D0"))))))




val safeproofu0 =
    safeproof(

       branchpf( // branch 1
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "0 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FN"),Var("FNP"),Var("D0"))))),

        branchpf( // branch 2
          List(
            parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
	    "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
	    "(K() * (fx() * nx() + fy() * ny()) * s() + " +
	    "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "D0 + K() * A * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
                List(Var("FN"),Var("FNP"),Var("D0"))))),

        arithT,  // branch 3

        branchpf( // branch 4
          List(
            parseFormula("TMP * K() * A = 1"),
            parseFormula("fx() * nx() + fy() * ny() + (FXP * nx() + FYP * ny()) * e() >= 0")),
          parseFormula(
            "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
            "(2 * (FXP * nx() + FYP * ny()) * " +
            "((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
            "(K() * (fx() * nx() + fy() * ny()) * s() + " +
            "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
          composelistT(
            unsubT(
              parseFormula(
                "(K() * 0 * FN)^2 - 2 * K() * 0 * FNP * D0 >= 0"),
              List(Var("FN"),Var("FNP"),Var("D0"))))),


       branchpf( // branch 5
         List(
           parseFormula("TMP * K() * (A * e() + 1 / 2 * (FXP * nx() + FYP * ny()) * e()^2) = 1")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "(-1 * ((qx() - px()) * nx() + (qy() - py()) * ny()) * TMP) * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() +  FNP * e()^2 * (1 / 2)) <= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 6
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "0 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("D0 + K() * Z * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
             List(Var("FNP"),Var("FN"),Var("D0"))))),


       branchpf( // branch 7
         List(
           parseFormula("FXP * nx() + FYP * ny() >= 0")),
         parseFormula(
           "(qx() - px()) * nx() + (qy() - py()) * ny() +" +
           "0 * " +
           "(K() * (fx() * nx() + fy() * ny()) * s() + " +
           "(1 / 2) * K() * (FXP * nx() + FYP * ny()) * s()^2) >= 0 "),
         composelistT(
           unsubT(
             parseFormula("FNP >= 0"),
             List(Var("FNP"))),
           unsubT(
             parseFormula("D0 <= 0"),
             List(Var("D0"))))))






val main =
   tryruleT(loopInduction(loopInv))<(
     easiestT,
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
                                         safeproofu1
                                         ,
                                         safeproofu1
                                       )
                                     ),
                                     safeproofub
                                   )
                                 ),
			         safeproofuc
                               )
                             ),
			     safeproofud
                           )
                         ),
			 safeproofu1
                        )),
		     safeproofu1b
		   )
		 ),
		 safeproofu
	       )
	     )
       	   )
       	 ),
	 safeproofu0 
       )
     ),
     easiestT
   )
}


        // branchpf(
        //   List(
        //     parseFormula(
        //       ...),
        //   parseFormula(
        //     ...),
        //   composelistT(
        //     unsubT(
        //       parseFormula(
        //         ...),
        //       List(...)))),
