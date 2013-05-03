object Script {

// a proof script for
// a theorem about the safety of the control algorithm that enforces
// multiple virtual fixtures in 3D, with force feedback
// uses multiplicative damping

val safestr = 
"(w() /= end() ==> "+
"(qx() - px(w())) * nx(w()) + (qy() - py(w())) * ny(w()) + " +
"(qz() - pz(w())) * nz(w()) + " +
"K() * (fx() * nx(w()) + fy() * ny(w()) + fz() * nz(w())) * GG * QQ + " +
"1 / 2 * K() * (FXP * nx(w()) + FYP * ny(w()) + FZP * nz(w())) * GG * QQ^2 >= 0)"

val oldsafestr = 
"(w() /= end() ==> "+
"(qx() - px(w())) * nx(w()) + (qy() - py(w())) * ny(w()) +" +
"(qz() - pz(w())) * nz(w())  >= 0)"

val oldsafestrW = 
"(WW /= end() ==> "+
"(qx() - px(WW)) * nx(WW) + (qy() - py(WW)) * ny(WW) + (qz() - pz(WW)) * nz(WW) >= 0)"

val safestrW = 
"(WW /= end() ==> "+
"(qx() - px(WW)) * nx(WW) + (qy() - py(WW)) * ny(WW) + (qz() - pz(WW)) * nz(WW) + " +
"K() * (fx() * nx(WW) + fy() * ny(WW) + fz() * nz(WW)) * GG * QQ + " +
"1 / 2 * K() * (FXP * nx(WW) + FYP * ny(WW) + FZP * nz(WW)) * GG * QQ^2 >= 0)"

val iteratestrA = "[w() := AA; { w() := next(w())}*] "

val iteratestrAZ = "[w() := AA; {?next(w()) /= ZZ; w() := next(w())}*] "


// This is the invariant for the outer loop of the controller. Each 
// loop is an epsilon-step in the machine where the controller enforces
// control and continuous time evolves

val loopInvOuter =
 parseFormula("K() > 0 & dd() > 0 & e() > 0 & g() >= 0 &" +
              "(forall i : B. nx(i)^2 + ny(i)^2 + nz(i)^2 = 1) & " +
              " next(end()) = end() & " +
              "(forall h : B . forall g :B . " +
	      "(next(h) /= end()) ==> (h /= g) ==> (next(h) /= next(g))) & " +

	      "[m() := first(); {m() := next(m())}*] " + 
	      "((m() /= end()) ==> " +
	      "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) + "+
	      " (qz() - pz(m())) * nz(m()) >= 0))")

// This is the invariant for the nested inner loop of the
// controller. This is a loop over the different virtal fixture
// boundaries, where each loop is the controller creating force
// feedback and enforcing safety for one boundary

val loopInvInner =
  parseFormula("K() > 0 & dd() > 0 & e() > 0 & " +
     "(forall i : B. nx(i)^2 + ny(i)^2 + nz(i)^2 = 1) & " +
     "next(end()) = end() & " +

     "(forall h : B . forall g :B . " +
     "(next(h) /= end()) ==> (h /= g) ==> (next(h) /= next(g))) & " +

     "([m() := ZZ; { m() := next(m()) }*] " + 
     "((m() /= end()) ==> " +
     "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) + " +
     " (qz() - pz(m())) * nz(m()) >= 0))) &" +


     "(GG >= 0)&" +

     "([m() := first(); { m() := next(m()) }*] " + 
     "((m() /= end()) ==> " +
     "((qx() - px(m())) * nx(m()) + (qy() - py(m())) * ny(m()) +" +
     " (qz() - pz(m())) * nz(m()) >= 0))) &" +

     "((ZZ /= first()) ==> (forall q : Real . ((0<=q)&(q<=e())) ==> " +
     "[w() := first(); {?next(w()) /= ZZ; w() := next(w())}*] " + 
     "((w() /= end()) ==> " +
     "((qx() - px(w())) * nx(w()) + (qy() - py(w())) * ny(w()) + " +
     "(qz() - pz(w())) * nz(w()) + "+
     "K() * (fx() * nx(w()) + fy() * ny(w()) + fz() * nz(w()))* GG * q + " +
     "(1 / 2) * K() * (FXP * nx(w()) + FYP * ny(w()) + FZP * nz(w())) * GG * q^2 >= 0))))")

// This is an invariant used for an induction in the postcondition
// branch of the nested inner loop. The postcondition is where
// continuous time evolves. This invariant helps rearrange the terms of
// the boxed modality so that we can unsubstitute common terms, i.e.
// fnp, fn, etc.. so that arithT completes quickly (see quickaritTh)

val rearrangeInv = parseFormula(
"(SS = s()) &" +
"(QXX = qx() + K() * fx() * GG * s() + 1/2 * K() * FXP * GG * s()^2) &"+
"(QYY = qy() + K() * fy() * GG * s() + 1/2 * K() * FYP * GG * s()^2) &"+
"(QZZ = qz() + K() * fz() * GG * s() + 1/2 * K() * FZP * GG * s()^2) &"+
       "(next(end()) = end()) & " +
       "(YY = end()) & " +
       "[w() := ZZ; {?next(w()) /= YY; w() := next(w())}*]" +
"((w() /= end()) ==> " +
"((qx() - px(w())) * nx(w()) + (qy() - py(w())) * ny(w()) + " +
" (qz() - pz(w())) * nz(w()) + " +
"K() * (fx() * nx(w()) + fy() * ny(w()) + fz() * nz(w())) * GG * SS + " +
"(1/2) * K() * (FXP * nx(w()) + FYP * ny(w()) + FZP * nz(w())) * GG * SS^2 >= 0))"
)

// This is an invariant used for an induction in the inductive "step"
// branch of the nested inner loop. This helps show that if the
// modalities in invariant loopInvInner hold at one step, then they
// hold at the next step as well.

// It essentially breaks the modality into two pieces: one that is the
// collection of virtual fixture boundaries that we made safe before,
// and the other is the collection of virtual fixture boundaries that
// we just made safe during this most recent step.

val breakInv = parseFormula("(" + iteratestrAZ + safestr + ") & (" +
safestrW + ") & (" +
iteratestrA + oldsafestr + ")")

val furtherdamped = parseFormula(iteratestrAZ + safestr)

val gqassumptionsstr = "GGN <= GG & GGN >= 0 & QQ = QQO &"

val furtherdampedctxt = parseFormula(
gqassumptionsstr + "(" + iteratestrAZ + safestr + ") & ("+
iteratestrA + oldsafestr + ")")


val obviousimpT =
	composelistT(
	  tryruleatT(hide)(RightP(1)),
	  substT*,
	  nonarithcloseT
	)

//"(forall h:B.forall g:B.next(h) /= end() ==> h /= g ==> next(h) /= next(g)) &" +

val onemore = parseFormula(
"(ZZ /= end()) & (OO = next(ZZ)) &" + "(" + safestrW + 
    " & ((AA /= ZZ) ==>" + iteratestrAZ + safestr + "))" )

// instantiate forall left
val fooz = new Tactic("fooz"){
  def apply(nd:Nodes.OrNode) = {
    val Sequent(sig, cs, ss) = nd.goal
    ss match {
      case List(Atom(R("/=", List(Fn(v,List(i)), _)))) =>
	  tryruleT(allLeft(i))(nd)
      case _ => None
    }
  }
}

// instantiate forall right
val fooz2 = new Tactic("fooz2"){
  def apply(nd:Nodes.OrNode) = {
    val Sequent(sig, cs, ss) = nd.goal
    ss match {
      case List(Atom(R("/=", List(_, Fn(v,List(i)))))) =>
	  tryruleT(allLeft(i))(nd)
      case _ => None
    }
  }
}

// instantiate forall left
val fooz3 = new Tactic("fooz3"){
  def apply(nd:Nodes.OrNode) = {

    val Sequent(sig, cs, ss) = nd.goal
    var res : Option[Term] = None

    for (z <- cs) {
       z match {
          case Atom(R("<=", List(Num(Exact.zero),i))) => res = Some(i)
          case _ => ()
       }
    }

    res match {
      case None => nilT(nd)
      case Some(tm) => tryruleT(allLeft(tm))(nd)
    }
  }
}

// instantiate forall left
val fooz4 = new Tactic("fooz4"){
  def apply(nd:Nodes.OrNode) = {

    val Sequent(sig, cs, ss) = nd.goal
    var res : Option[Term] = None

    for (z <- cs) {
       z match {
          case Atom(R("=", List(i,Fn("next", List(j))))) =>
	       res = Some(j)
          case _ => ()
       }
    }

    res match {
      case None => nilT(nd)
      case Some(tm) => tryruleT(allLeft(tm))(nd)
    }
  }
}

// instantiate forall left
val fooz5 = new Tactic("fooz5"){
  def apply(nd:Nodes.OrNode) = {

    val Sequent(sig, cs, ss) = nd.goal
    var res : Option[Term] = None

    for (z <- cs) {
       z match {
          case Atom(R("/=", List(i,Fn("end", List())))) =>
	       res = Some(i)
          case _ => ()
       }
    }

    res match {
      case None => nilT(nd)
      case Some(tm) => tryruleT(allLeft(tm))(nd)
    }
  }
}



val quickarithT : Tactic = 
    composelistT(
      substT*,
      nullarizeT*,
      tryruleT(andLeft)*,
      (unsubT(
         parseFormula("D0 + K() * AA * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) | unitT),
      arithT
    )

val quickarith2T : Tactic = 
    composelistT(
      substT*,
      nullarizeT*,
      tryruleT(andLeft)*,
      (unsubT(
         parseFormula("D0 + K() * FN * AA * SS + (1 / 2) * K() * FNP * AA* (SS)^2 >= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) | 
       unsubT(
         parseFormula("D0 + K() * AA * (FN * e() + FNP * e()^2 * (1 / 2)) >= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) |
       unsubT(
         parseFormula("D0 + K() * AA * (FN * e() + FNP * e()^2 * (1 / 2)) <= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) |
       unsubT(
         parseFormula("(K() * AA * FN)^2 - 2 * K() * AA * FNP * D0 <= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) |
       unsubT(
         parseFormula("(K() * AA * FN)^2 - 2 * K() * AA * FNP * D0 >= 0"),
	 List(Var("FN"),Var("FNP"),Var("D0"))) |
       unsubT(
         parseFormula("FNP <= 0"),
	 List(Var("FNP"))) |
       unsubT(
         parseFormula("FNP >= 0"),
	 List(Var("FNP"))) | unitT),
       arithT
    )


val identiboxT = 
      composelistT(
        tryruleT(seq)*,
	substT*,
        tryruleT(renameAssign("ii")),
	tryruleatT(renameAssign("ii"))(RightP(0)),
	substT*,
	nonarithcloseT
      )


val nextloopT = 
    composelistT(
      tryruleT(iterate),
      tryruleT(andLeft),
      tryruleT(seq)*,
      identiboxT
    )

val onestepT = 
	    composelistT(
	      tryruleT(seq)*,
	      tryruleT(check)*,
	      tryruleT(impRight)*,
	      tryruleT(assign)*,
    	    tryruleT(andRight)<(
	      tryruleT(andRight)<(
	        easiestT,
		composelistT(
		   tryruleT(iterate),
	      	   tryruleT(andLeft)*,
	      	   tryruleT(seq)*,
	      	   tryruleT(check),
	      	   tryruleatT(impLeft)(LeftP(5))<(
	              composelistT(
		  	  identiboxT
		      ),
		      composelistT(
	      	         tryruleatT(hide)(RightP(1)),
		      	 substT*,
		      	 nonarithcloseT
		      )
	      	   )
		)
	      ),
	      composelistT(
	        tryruleatT(reorder)(LeftP(5)),
		nextloopT
	      ))
	    )


val onestep2T = 
	  composelistT(
	      tryruleT(seq)*,
	      tryruleT(check)*,
	      tryruleT(impRight)*,
	      tryruleatT(assign)(RightP(0)),
	      tryruleT(andRight)<(
	        easiestT,
		tryruleT(andRight)<(
		  nonarithcloseT,
		  composelistT(
		    tryruleT(impRight),
		    tryruleT(seq)*,
		    substT*,
		    cutT(StandardCut,
		      parseFormula("next(AA) /= next(BB)"),
		      parseFormula("AA /= BB | AA = BB"))<(
		        composelistT(
			  tryruleT(orRight),
			  tryruleatT(notEquals)(RightP(0)),
			  tryruleT(not),
			  nonarithcloseT
			),
			tryruleT(orLeft)<(
			  composelistT(
			    tryruleatT(hide)(LeftP(3)),
			    tryruleT(impLeft)<(
			    composelistT(
			      tryruleT(seq)*,
			      tryruleT(assign),
			      tryruleT(iterate),
			      tryruleT(andLeft)*,
			      tryruleT(seq)*,
			      tryruleT(check),
			      tryruleatT(impLeft)(LeftP(5))<(
			        composelistT(
				  tryruleatT(commuteEquals)(LeftP(3)),
				  identiboxT
				),
				composelistT(
				  tryruleatT(hide)(RightP(1)),
				  substT*,
				  nonarithcloseT
				)
			      )
			    ),
			      composelistT(
			        tryruleatT(hide)(RightP(1)),
				nonarithcloseT
			      )
			    )
			  ),
			  composelistT(
			    tryruleatT(hide)(LeftP(5)),
			    tryruleatT(hide)(LeftP(3)),
			    tryruleatT(hide)(RightP(0)),
			    substT*,
			    nonarithcloseT
			  )
			)
		      )
		  )
		)
	      )
          )


val concludeT =
 	    composelistT(
	      tryruleT(impRight)*,
	      hpalphaT*,
	      tryruleT(iterate),
	      tryruleT(andLeft),
	      tryruleatT(hide)(LeftP(5)),
	      substT*,
	      tryruleT(impLeft)<(
	        composelistT(
		  tryruleT(iterate),
		  tryruleT(andLeft),
		  tryruleatT(hide)(LeftP(5)),
		  tryruleT(impLeft)<(
		    composelistT(
		      tryruleatT(hide)(LeftP(0)),
		      quickarith2T
		    ),
		    composelistT(
		      tryruleatT(hide)(RightP(1)),
		      substT*,
		      nonarithcloseT
		    )
		  )
		),
	        nonarithcloseT),
	      nilT
	    )


val conclude2T =
 	    composelistT(
	      tryruleT(impRight)*,
	      hpalphaT*,
	      tryruleT(iterate),
	      tryruleT(andLeft),
	      tryruleatT(hide)(LeftP(3)),
	      substT*,
	      tryruleT(impLeft)<(
	        nonarithcloseT,
	        nonarithcloseT),
	      nilT
	    )



val equivboxT = 
composelistT(
  tryruleT(seq)*,
  tryruleatT(assign)(RightP(0)),
  cutmT(StandardCut,
  List(parseFormula("AA = GGN"),
       parseFormula("GGO >= 0")),
  parseFormula("GGN <= GGO"))<(
    composelistT(
      substT*,
      tryruleatT(hide)(LeftP(33+2)),
      tryruleatT(hide)(LeftP(32+2)),
      tryruleatT(hide)(LeftP(31+2)),
      tryruleatT(hide)(LeftP(30+2)),
      tryruleatT(hide)(LeftP(29+2)),
      tryruleatT(hide)(LeftP(28+2)),
      tryruleatT(hide)(LeftP(27+2)),
      tryruleatT(hide)(LeftP(26+2)),
      tryruleatT(hide)(LeftP(25+2)),
      tryruleatT(hide)(LeftP(24+2)),
      tryruleatT(hide)(LeftP(23+2)),
      tryruleatT(hide)(LeftP(22+2)),
      tryruleatT(hide)(LeftP(21+2)),
      tryruleatT(hide)(LeftP(20+2)),
      tryruleatT(hide)(LeftP(19+2)),
      tryruleatT(hide)(LeftP(18+2)),
      tryruleatT(hide)(LeftP(17+2)),
      tryruleatT(hide)(LeftP(16+2)),
      tryruleatT(hide)(LeftP(15+2)),
      tryruleatT(hide)(LeftP(14+2)),
      tryruleatT(hide)(LeftP(13+2)),
      tryruleatT(hide)(LeftP(12+2)),
      tryruleatT(hide)(LeftP(11+2)),
      tryruleatT(hide)(LeftP(10+2)),
      tryruleatT(hide)(LeftP(9+2)),
      tryruleatT(hide)(LeftP(7)),
      tryruleatT(hide)(LeftP(6)),
      tryruleatT(hide)(LeftP(5)),
      tryruleatT(hide)(LeftP(4)),
      tryruleatT(hide)(LeftP(3)),
      tryruleatT(hide)(LeftP(2)),
      tryruleatT(hide)(LeftP(1)),
      tryruleatT(hide)(LeftP(0)),
      nullarizeT*,	      
      arithT
    ),
  composelistT(
    substT*,

  newestT("fzp",
     fzp_string =>
  newestT("fyp",
     fyp_string =>
         newestT("fxp",
            fxp_string =>
    unifyT(parseFormula("GGN <= GG"),
          Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
          Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
       	   Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
 	    furtherdampedctxt))),
(w => unifyT(parseFormula("QQ = QQO"), w,
   (x => unifyT(parseFormula("ZZ /= end()"), x,
      (y => unifyT(parseFormula("AA = first()"), y,
         (z => tryruleT(loopInduction(z))))))))))))))<(
	 tryruleT(andRight)<(
	   tryruleT(andRight)<(
	     tryruleT(andRight)<(
	       tryruleT(andRight)<(
	         composelistT(
		   tryruleatT(hide)(LeftP(35+2)),
		   tryruleatT(hide)(LeftP(34+2)),
		   tryruleatT(hide)(LeftP(33+2)),
		   tryruleatT(hide)(LeftP(32+2)),
		   tryruleatT(hide)(LeftP(31+2)),
		   tryruleatT(hide)(LeftP(30+2)),
		   tryruleatT(hide)(LeftP(29+2)),
		   tryruleatT(hide)(LeftP(28+2)),
		   tryruleatT(hide)(LeftP(27+2)),
		   tryruleatT(hide)(LeftP(26+2)),
		   tryruleatT(hide)(LeftP(25+2)),
		   tryruleatT(hide)(LeftP(24+2)),
		   tryruleatT(hide)(LeftP(23+2)),
		   tryruleatT(hide)(LeftP(22+2)),
		   tryruleatT(hide)(LeftP(21+2)),
		   tryruleatT(hide)(LeftP(20+2)),
		   tryruleatT(hide)(LeftP(19+2)),
		   tryruleatT(hide)(LeftP(18+2)),
		   tryruleatT(hide)(LeftP(17+2)),
		   tryruleatT(hide)(LeftP(16+2)),
		   tryruleatT(hide)(LeftP(15+2)),
		   tryruleatT(hide)(LeftP(14+2)),
		   tryruleatT(hide)(LeftP(13+2)),
		   tryruleatT(hide)(LeftP(12+2)),
		   tryruleatT(hide)(LeftP(11+2)),
		   tryruleatT(hide)(LeftP(10+2)),
		   tryruleatT(hide)(LeftP(9+2)),
		   tryruleatT(hide)(LeftP(8)),
		   tryruleatT(hide)(LeftP(7)),
		   tryruleatT(hide)(LeftP(6)),
		   tryruleatT(hide)(LeftP(5)),
		   tryruleatT(hide)(LeftP(4)),
		   tryruleatT(hide)(LeftP(3)),
		   tryruleatT(hide)(LeftP(2)),
		   tryruleatT(hide)(LeftP(1)),
		   nullarizeT*,
		   arithT
		 ),
		 composelistT(
		   tryruleatT(allLeft(Fn("first",List())))(LeftP(21)),
		   tryruleatT(reorder)(LeftP(20)),
		   fooz5,
		   tryruleT(impLeft)<(
		     tryruleT(impLeft)<(
		       composelistT(
		         tryruleatT(hide)(LeftP(38)),
		         tryruleatT(hide)(LeftP(36)),
		         tryruleatT(hide)(LeftP(34)),
		         tryruleatT(hide)(LeftP(32)),

		         tryruleatT(hide)(LeftP(30)),
		         tryruleatT(hide)(LeftP(29)),
		         tryruleatT(hide)(LeftP(27)),
		         tryruleatT(hide)(LeftP(25)),

		         tryruleatT(hide)(LeftP(23)),

			 tryruleatT(hide)(LeftP(18)),
			 tryruleatT(hide)(LeftP(17)),
			 tryruleatT(hide)(LeftP(16)),

		         tryruleatT(hide)(LeftP(11)),

			 tryruleatT(hide)(LeftP(8)),
			 tryruleatT(hide)(LeftP(5)),
			 tryruleatT(hide)(LeftP(1)),
			 quickarith2T
		       ),
		       obviousimpT
		     ),
		     obviousimpT
		   )		 
		 )
	       ),
	       nonarithcloseT
	     ),
	     identiboxT
	   ),
	   composelistT(
	     tryruleatT(reorder)(LeftP(21+2)),
	     identiboxT
	   )
	 ),
	 composelistT(
	      tryruleT(andLeft)*,
	      tryruleatT(reorder)(LeftP(2)),
	      onestepT
	 ),
	 composelistT(
	   tryruleT(andLeft)*,
	   tryruleT(seq)*,
	   tryruleT(assign)*,
	   tryruleatT(iterate)(LeftP(3)),
	   tryruleT(andLeft)*,
	   tryruleatT(hide)(LeftP(4)),
	   tryruleatT(iterate)(LeftP(4)),
	   tryruleT(andLeft)*,
	   tryruleatT(hide)(LeftP(5)),
	   tryruleT(impRight),
	   tryruleT(impLeft)<(
	     tryruleT(impLeft)<(
	       composelistT(
       	         tryruleatT(hide)(LeftP(0)),
	         quickarith2T
	       ),
       	       composelistT(
	         tryruleatT(hide)(RightP(1)),
		 tryruleT(notEquals)*,
		 tryruleT(not)*,
		 tryruleatT(commuteEquals)(LeftP(6)),
		 substT*,
		 nonarithcloseT)
	     ),
     	     composelistT(
	         tryruleatT(hide)(RightP(1)),
		 tryruleT(notEquals)*,
		 tryruleT(not)*,
		 tryruleatT(commuteEquals)(LeftP(6)),
		 substT*,
		 nonarithcloseT)
	   )
	 )
       )
     )
)



// This is the proof to help complete the inner loop's postcondition
// that shows one modality with our desired
// postcondition implies another, whose terms are identical but
// rearranged.

val rearrangepf = 
composelistT(
newestT("g",
   g_string =>
 newestT("fzp",
    fzp_string =>
 newestT("fyp",
    fyp_string =>
        newestT("fxp",
           fxp_string =>
 newestT("qx",
    qx_string =>
        newestT("qy",
           qy_string =>
        newestT("qz",
           qz_string =>
   unifyT(parseFormula("SS = s()"),
           Prover.substitute_Formula("GG", Fn(g_string, Nil),
           Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
           Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
      	   Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
      	   Prover.substitute_Formula("QXX", Fn(qx_string, Nil),
      	   Prover.substitute_Formula("QYY", Fn(qy_string, Nil),
      	   Prover.substitute_Formula("QZZ", Fn(qz_string, Nil),
	    rearrangeInv))))))),
(x => unifyT(parseFormula("YY = end()"), x,
   (y => unifyT(parseFormula("ZZ = first()"), y,
      (z => tryruleT(loopInduction(z)))))))))))))))<(
	     tryruleT(andRight)<(
	       easiestT,
	       identiboxT // added here 1
	     ),
	     composelistT(
	       tryruleT(andLeft)*,
	       tryruleT(assign),
	       tryruleT(andRight)<(
	          easiestT,
		  composelistT(
		    tryruleT(seq)*,
		    tryruleatT(hide)(LeftP(3)),
		    tryruleatT(hide)(LeftP(2)),
		    tryruleatT(hide)(LeftP(1)),
		    tryruleatT(hide)(LeftP(0)),
		    tryruleatT(assign)(LeftP(2)),
		    tryruleT(iterate),
		    tryruleT(andLeft),
		    tryruleT(seq)*,
		    tryruleT(check)*,		    
		    tryruleatT(reorder)(LeftP(1)),
		    newestT("w",
		      w_string =>
		    cutT(StandardCut,parseFormula("II = end()"),
		         Prover.substitute_Formula("WW", Fn(w_string, Nil),
			 parseFormula("next(WW) = II | next(WW) /= II"))))<(
		      composelistT(
		        tryruleT(orRight),
		        tryruleT(notEquals),
			tryruleT(not),
			nonarithcloseT
		      ),
		      tryruleT(orLeft)<(
		        composelistT(
			  tryruleatT(hide)(LeftP(4)),
			  tryruleatT(hide)(LeftP(3)),
			  substT*,
			  tryruleT(assign)*,
			  unifyT(parseFormula("WW = next(MM)"),
			    parseFormula("next(end()) = end() & WW = end()"),
			    ( y => tryruleT(loopInduction(y))))<(
			      composelistT(substT*,easiestT),
			      composelistT(
			         substT*,
				 easiestT,
				 tryruleatT(substitute)(LeftP(2)),
				 tryruleatT(substitute)(LeftP(2)),
				 nonarithcloseT
			      ),
			      composelistT(
			         substT*,
				 easiestT,
				 tryruleT(notEquals),
				 tryruleT(not),
				 substT*,
				 nonarithcloseT
			      )
			    )
			),
			composelistT(
			  tryruleatT(hide)(LeftP(3)),
			  tryruleT(impLeft)<(
			    composelistT(
			       tryruleatT(commuteEquals)(LeftP(5)),
			       substT*,
			       identiboxT // added here
			    ),
			    composelistT(
			       tryruleatT(hide)(RightP(1)),
			       nonarithcloseT
			    )
			  )
			)
		      )
		    )
		  )
	       )
	     ),
	     composelistT(
	       tryruleT(andLeft)*,
	       tryruleT(impRight)*,
	       tryruleT(seq)*,
	       tryruleT(assign)*,
	       tryruleT(iterate),
	       tryruleT(andLeft),
	       tryruleatT(hide)(LeftP(8)),
	       substT*,
	       tryruleT(impLeft)<(
	         composelistT(tryruleatT(hide)(LeftP(0)),nullarizeT*,arithT),
		 composelistT(tryruleatT(hide)(RightP(1)),nonarithcloseT)
	       )
	     )
   )
)


val uglyrotation : Tactic =
   composelistT(
//
// Rotation to allow proving of zero branch cluster
//
// The zero-branch cluster needs another piece of context.
// We thread the necessary state through the proof in a
// straightforward manner up to this point. Until this point,
// the proof takes apart the structure of the HP, and organizes
// itself around this structure, preparing to prove its safety property.
// Starting at this point, the proof begins to refer to specific pieces
// of context, and for its success depends on the order of antecedents.
// Consequently, threading the state through past this point will break
// the rest of the proof, and require revisiting all of its different
// cuts and inductions.
//
// To avoid this, I observe that one of the antecedents, necessary for 
// the postcondition in one of the outer inductive loops, has been carried
// forward to this point. Replacing it with the new piece of context leaves
// the positions of each of the other antecedents should leave the rest
// of the proof intact, while making this context available to whatever
// branches need it to close.
//
// It goes without saying that this is extremely brittle.
//

      tryruleT(assign),
      tryruleT(iterate),
      tryruleatT(andLeft)(LeftP(14)),
      tryruleatT(hide)(LeftP(15)),
      tryruleatT(hide)(LeftP(13)),
      tryruleatT(reorder)(LeftP(13)),
      tryruleatT(reorder)(LeftP(34)),
      cutT(StandardCut, parseFormula("AA = WW"), 
         parseFormula("forall i : B . " + oldsafestrW))<(
	 composelistT(
	   substT,
	   tryruleT(allRight),
	   nonarithcloseT
	 ),
	 composelistT(
	   substT,
           tryruleatT(hide)(LeftP(1)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
           tryruleatT(reorder)(LeftP(13)),
	   unitT // ready to go
	 )
      )
   )


// Used in the inductive "step" part of induction for the nested inner
// loop. Show that the if second modal term in the nested inner loop's
// invariant hold in one step, it holds in the next.

val inductivesteppf : Tactic =
    composelistT(

      uglyrotation, // see notes above

      tryruleT(impRight),
      tryruleT(allRight),
      tryruleT(impRight),
      substT*,

	  cutT(StandardCut, parseFormula("AA = next(BB)"),
	       parseFormula("(BB = first()) | (BB /= first())"))<(
		composelistT(
		  tryruleT(orRight),
		  tryruleT(notEquals)*,
		  tryruleatT(not)(RightP(1)),
		  nonarithcloseT
		),
		composelistT(
		  tryruleT(orLeft)<(
      		    composelistT(
		      tryruleatT(hide)(LeftP(16+2)),
		      tryruleatT(hide)(LeftP(15+2)),
		      substT*,
		      tryruleT(andLeft),
		      tryruleT(seq)*,
		      tryruleatT(assign)(RightP(0)),
		      tryruleatT(iterate)(RightP(0)),
		      tryruleT(andRight)<(
		        composelistT(
			   substT*,
			   tryruleatT(allLeft(Fn("first",List())))(LeftP(13)),
			   tryruleatT(hide)(LeftP(14)),
			   tryruleatT(allLeft(Fn("first",List())))(LeftP(14)),
			   tryruleatT(hide)(LeftP(15)),
                           tryruleT(impRight),
			   tryruleT(impLeft)<(
			     composelistT(
			       tryruleatT(hide)(LeftP(24)),
			       tryruleatT(hide)(LeftP(23)),
			       tryruleatT(hide)(LeftP(22)),
			       tryruleatT(hide)(LeftP(20)),
			       tryruleatT(hide)(LeftP(19)),
			       tryruleatT(hide)(LeftP(18)),
			       tryruleatT(hide)(LeftP(17)),
			       tryruleatT(hide)(LeftP(12)),
			       tryruleatT(hide)(LeftP(11)),
			       tryruleatT(hide)(LeftP(5)),
			       tryruleatT(hide)(LeftP(0)),
			       quickarith2T
			     ),
			     composelistT(
			        tryruleatT(hide)(RightP(1)),
				nonarithcloseT
			     )
			   )
			),
		        composelistT(
			   hpalphaT*,
			   tryruleatT(reorder)(LeftP(6+2)),
			   tryruleatT(reorder)(LeftP(6+2)),
			   tryruleatT(hide)(RightP(0)),
			   substT*,
			   nonarithcloseT
			)
	 	      )
		    ),
// got to here
          tryruleT(impLeft)<(
            composelistT(
	        tryruleT(andLeft),
		tryruleT(seq)*,	
		tryruleatT(assign)(RightP(0)),
		tryruleatT(reorder)(LeftP(22+2)),
newestT("g",
 g_string =>
		cutmT(StandardCut,
List(parseFormula("0 <= QQ"),
     parseFormula("WW /= first()"),
     parseFormula("FNP = FXP * nx(AA) + FYP * ny(BB) + FZP * nz(BB)")),
      Prover.substitute_Formula("GG", Fn(g_string, Nil),
        parseFormula(safestrW))))<(
   composelistT(
      tryruleatT(allLeft(Fn("first",List())))(LeftP(17)),
      tryruleatT(hide)(LeftP(18)),
      tryruleT(impLeft)<(
        composelistT(
	  tryruleT(impRight),
	  tryruleatT(hide)(LeftP(34)), 
	  tryruleatT(hide)(LeftP(32)), 
	  tryruleatT(hide)(LeftP(30)), 
	  tryruleatT(hide)(LeftP(28)), 
	  tryruleatT(hide)(LeftP(26)), 
	  tryruleatT(hide)(LeftP(25)), 
	  tryruleatT(hide)(LeftP(23)), 
	  tryruleatT(hide)(LeftP(21)),  // get rid of boxen
	  tryruleatT(hide)(LeftP(20)),
	  tryruleatT(hide)(LeftP(18)),
	  tryruleatT(hide)(LeftP(17)),
	  tryruleatT(hide)(LeftP(13)),
	  tryruleatT(hide)(LeftP(12)),
	  tryruleatT(hide)(LeftP(11)),
	  tryruleatT(hide)(LeftP(6)),
	  tryruleatT(hide)(LeftP(3)),
	  tryruleatT(hide)(LeftP(0)),
	  substT*,
	  quickarith2T
	),
	composelistT(
	  tryruleatT(hide)(RightP(1)),
	  nonarithcloseT
	)
      )
   ),

  newestT("fzp",
      fzp_string =>
  newestT("fyp",
      fyp_string =>
  newestT("fxp",
      fxp_string =>
  newestT("g",
      g_string =>
  unifyT(parseFormula("ZZ = next(WW)"),
      Prover.substitute_Formula("GG", Fn(g_string, Nil),
        Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
          Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
            Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
	     breakInv)))),
    (x => unifyT(parseFormula("QQ <= e()"), x,
       (y => unifyT(parseFormula("AA = first()"), y,
          (z => tryruleT(loopInduction(z))))))))))))<(
	tryruleT(andRight)<(
  	  tryruleT(andRight)<(
	    composelistT(
	      fooz3,
	      tryruleatT(hide)(LeftP(21+2)),
	      tryruleT(impLeft)<(
	         composelistT(
                  newestT("fxp", fxp_string =>
                  newestT("fyp", fyp_string =>
                  newestT("fzp", fzp_string =>
                  newestT("g", g_string =>
		      cutmT(StandardCut,
		         List(
			      parseFormula(safestrW),
			      parseFormula("ZZ /= end()")
			      ),
Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
Prover.substitute_Formula("GG", Fn(g_string, Nil),
Prover.substitute_Formula("AA", Fn("first", Nil),
			 furtherdamped))))))))))<(

// this cut asserts (using a box modality) that all previous
// boundaries are still safe given the update to damping that we made
// with the current boundary
 composelistT(
   tryruleT(seq)*,
   tryruleatT(assign)(RightP(0)),
   tryruleatT(reorder)(LeftP(36)),


newestT("w", w_string =>
newestT("fxp", fxp_string =>
  newestT("fyp", fyp_string =>
    newestT("fzp", fzp_string =>
     newestT("q", q_string =>
       unifyT(parseFormula("QQO <= e()"),
Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
Prover.substitute_Formula("QQ", Fn(q_string, Nil),
Prover.substitute_Formula("AA", Fn(w_string, Nil),
			 furtherdampedctxt))))),
        (v => unifyT(parseFormula("ZZ /= end()"), v,
          (x => unifyT(parseFormula("GGN = GG"), x,
	    (y => tryruleT(loopInduction(y)))))))))))))<(
	    tryruleT(andRight)<(
	      tryruleT(andRight)<(
	        tryruleT(impLeft)<(
		    composelistT(
		       tryruleatT(reorder)(LeftP(19)),
		       fooz5,
		       tryruleatT(hide)(LeftP(1)),
		       tryruleatT(allLeft(Fn("first",List())))(LeftP(21)),
		       tryruleT(impLeft)<(
		         composelistT(
			     tryruleatT(hide)(LeftP(40)), 
			     tryruleatT(hide)(LeftP(39)), 
			     tryruleatT(hide)(LeftP(38)), 
			     tryruleatT(hide)(LeftP(37)), 
			     tryruleatT(hide)(LeftP(35)), 
			     tryruleatT(hide)(LeftP(33)), 
			     tryruleatT(hide)(LeftP(31)), 
			     tryruleatT(hide)(LeftP(29)), 
			     tryruleatT(hide)(LeftP(28)), 
			     tryruleatT(hide)(LeftP(26)), 
			     tryruleatT(hide)(LeftP(24)), 
			     tryruleatT(hide)(LeftP(22)), 
			     tryruleatT(hide)(LeftP(21)), 
			     tryruleatT(hide)(LeftP(17)), 
			     tryruleatT(hide)(LeftP(16)), 
			     tryruleatT(hide)(LeftP(10)), 
			     tryruleatT(hide)(LeftP(7)), 
			     tryruleatT(hide)(LeftP(4)), 
			     // try this:
			     tryruleT(andRight)<(
			        tryruleT(andRight)<(
				   quickarith2T,
				   quickarith2T
				),
			        quickarith2T
			     )
			 ),
		         obviousimpT
		       )
		     ),
		    easiestT
		),
		equivboxT
	      ),
	      composelistT(
	        tryruleatT(reorder)(LeftP(21+2)), 
		identiboxT
	      )
	    ),
	    composelistT(
	      tryruleT(andLeft)*,
	      tryruleatT(reorder)(LeftP(2)),
	      onestepT
	    ),
	    composelistT(
	      tryruleT(andLeft)*,
	      tryruleatT(reorder)(LeftP(2)),
	      concludeT
	    )
	 )
),

// we use the modal assertion that we just made, plus an assertion
// about the next boundary that is currently being controlled for, to
// assert the inductive step: if in the current step all previous
// boundaries were safe, then in the next step all previous boundaries
// are safe, plus one more

composelistT(

tryruleT(seq)*,
tryruleatT(assign)(RightP(0)),
substT*,

newestT("fxp", fxp_string =>
  newestT("fyp", fyp_string =>
    newestT("fzp", fzp_string =>
       unifyT(parseFormula("AA = first()"),
Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
			 onemore))),
        (v => unifyT(parseFormula("OO = next(ZZ)"), v,
          (x => unifyT(parseFormula(safestrW), x,
	    (y => tryruleT(loopInduction(y)))))))))))<(
	    tryruleT(andRight)<(
	      easiestT,
	      tryruleT(andRight)<(
	        easiestT,
		composelistT(tryruleT(impRight),identiboxT)
              )
	    ),
	    composelistT(
	      tryruleT(andLeft)*,
	      tryruleatT(reorder)(LeftP(2)),
	      onestep2T
	    ),
	    composelistT(
	      tryruleT(andLeft)*,
	      tryruleatT(reorder)(LeftP(3)),
	      tryruleT(impRight),
	      cutmT(StandardCut,
	         List(parseFormula("WW /= end()"),
		      parseFormula("JJ = next(II)")),
		 parseFormula("WW = II | WW /= II"))<(
	          composelistT(
		    tryruleT(orRight),
		    tryruleatT(notEquals)(RightP(1)),
		    tryruleT(not),
		    nonarithcloseT
		  ),
		  tryruleT(orLeft)<(
		    composelistT(
		      tryruleatT(hide)(LeftP(2)),
		      substT*,
		      tryruleT(impLeft)<(
		        nonarithcloseT,
			nonarithcloseT
		      )
		    ),
		    tryruleT(impLeft)<(
			conclude2T,
		        composelistT(
			  tryruleatT(hide)(RightP(1)),
			  nonarithcloseT
			)
		    )
		  )
	      )
	    )
)
)
) // end of cut
	      	),
	      	composelistT(
		  tryruleatT(hide)(LeftP(19)),
	      	  tryruleatT(hide)(RightP(1)),
		  substT*,
	      	  easiestT
	      	)
	      )
	    ),
	    composelistT(
	      tryruleT(impRight),
	      tryruleT(impLeft)<(
	        nonarithcloseT,
		nonarithcloseT
	      )
	    )
	  ),
	  identiboxT
	),
	composelistT( // inductive step
	  tryruleT(seq)*,
	  tryruleT(andLeft)*,
	  hpalphaT*,
	  tryruleT(andRight)<(
	    tryruleT(andRight)<(
	      composelistT(
		    tryruleT(seq)*,
		    substT*,
		    //iterate here
		    tryruleT(iterate),
		    tryruleT(andLeft),
		    tryruleT(seq)*,
		    tryruleT(check)*,
		    tryruleatT(impLeft)(LeftP(2))<(
		      identiboxT,
		      composelistT(
		        tryruleatT(hide)(RightP(1)),
			substT*,
			nonarithcloseT
		      )
		    )
	      ),
	      easiestT
	    ),
	    composelistT(
	      tryruleatT(reorder)(LeftP(3)),
	      nextloopT
	    )
	  )
	),
	  composelistT( // postcondition
	    tryruleT(andLeft)*,
	    tryruleT(seq),
	    tryruleT(assign),
	    tryruleT(iterate),
	    tryruleT(andLeft),
	    tryruleatT(hide)(LeftP(1)),
	    substT*,
	    nonarithcloseT
	  )
	) // end of induction
) // end of cut

	),
		      composelistT(
		        tryruleatT(hide)(RightP(1)),
			nonarithcloseT
		      )
		    )
		  )
		)
	  ),
	       nilT,
        nilT
    )

val tailstepT : Tactic =
     composelistT(
          tryruleT(seq)*,
	  substT,

	  tryruleatT(assign)(LeftP(3)),
	  tryruleatT(iterate)(LeftP(3)),
	  tryruleT(andLeft),
	  tryruleT(seq)*,
	  tryruleT(check),
	  tryruleT(impLeft)<(
	    composelistT(
	      tryruleatT(reorder)(LeftP(5)),
	      tryruleatT(renameAssign("ii"))(LeftP(5)),
	      tryruleatT(renameAssign("ii"))(RightP(0)),
	      substT*,
	      nonarithcloseT
	    ),
	    composelistT(
	      tryruleatT(hide)(RightP(1)),
	      substT,
	      tryruleT(notEquals)*,
	      tryruleatT(not)(RightP(0)),
	      tryruleatT(not)(LeftP(1)),
	      substT,
	      nonarithcloseT
	    )
	  )
	)



val brT : Tactic = 
         composelistT(
	   tryruleatT(seq)(RightP(0)),
	   tryruleatT(check)(RightP(0)),
	   tryruleT(impRight),
	   tryruleatT(assign)(RightP(0))*,
	   tryruleT(andRight)<(
	     tryruleT(andRight)<(
	       tryruleT(andRight)<(
	         tryruleT(andRight)<(
		   easiestT,
		   composelistT(
		     tryruleT(assign),
		     tryruleT(iterate),
		     tryruleT(andLeft)*,
		     identiboxT
		   )
		 ),
		 composelistT(
		   tryruleT(assign),
		   tryruleT(iterate),
		   tryruleatT(andLeft)(LeftP(14)),
		   tryruleatT(hide)(LeftP(15)),
		   tryruleatT(reorder)(LeftP(11)),
		   fooz5,
		   substT*,
		   tryruleT(impLeft)<(
		     composelistT(
		       tryruleatT(hide)(LeftP(31)),
		       tryruleatT(hide)(LeftP(29)),
		       tryruleatT(hide)(LeftP(27)),
		       tryruleatT(hide)(LeftP(25)),
		       tryruleatT(hide)(LeftP(23)),
		       tryruleatT(hide)(LeftP(21)),
		       tryruleatT(hide)(LeftP(19)),
		       tryruleatT(hide)(LeftP(17)),
		       tryruleatT(hide)(LeftP(16)),

		       tryruleatT(hide)(LeftP(13)),
		       tryruleatT(hide)(LeftP(12)),
		       tryruleatT(hide)(LeftP(8)),
		       tryruleatT(hide)(LeftP(7)),
		       tryruleatT(hide)(LeftP(6)),
		       tryruleatT(hide)(LeftP(1)),
		       substT*,
		       quickarith2T
		     ),
		     composelistT(
		       tryruleatT(hide)(RightP(1)),
		       nonarithcloseT
		     )
		   )
		 )
	       ),
	       composelistT(
	         tryruleatT(hide)(LeftP(14)),
		 identiboxT
	       )
	     ),
	     inductivesteppf
	   )
	 )


val easybranchT :  Tactic => Tactic = 
     foo =>
     composelistT(
       tryruleatT(seq)(RightP(0))*,
       tryruleT(check),
       tryruleT(impRight),

       tryruleT(assignAnyRight)*,
       tryruleT(check)*,
       tryruleT(impRight)*,

       tryruleatT(assign)(RightP(0)),
       tryruleatT(choose)(RightP(0)),
       tryruleT(andRight)<(
         brT
	 ,
	 brT)
       )




val hpalphaRT : Tactic =
   (tryruleT(seq) | 
    tryruleatT(assign)(RightP(0)) |
    tryruleatT(check)(RightP(0)) |
    tryruleatT(assignAnyRight)(RightP(0)) |
    tryruleatT(qassign)(RightP(0)) |
    tryruleatT(choose)(RightP(0)) |

    tryruleT(impRight) |
    tryruleT(allRight) |
    tryruleT(existsLeft) |
    tryruleT(orRight) |
    tryruleT(not)
  
    )

//    tryruleT(andLeft) |


val safeproofz : Tactic => Tactic = 
   solvebranch => 
     composelistT(
       hpalphaRT*,
       substT,
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleatT(reorder)(LeftP(24)),
       tryruleT(andRight)<(
       composelistT(
         hpalphaRT*,
           tryruleT(andRight)<(
             composelistT(
               hpalphaRT*,
               tryruleT(andRight)<(
                 composelistT(
                   hpalphaRT*,
                   tryruleT(andRight)<(
                     composelistT(
                       hpalphaRT*,
                       tryruleT(andRight)<(
                         composelistT(
                           hpalphaRT*,
                           tryruleT(andRight)<(
                             // branch 1
                             solvebranch
,
                             // branch 2
			     solvebranch
			     )),
                         //branch 3
                         solvebranch
			 )),
                     // branch 4
                     solvebranch
		     )),
                 // branch 5
                 solvebranch
		 )),
             // branch 6
	     solvebranch
	     )),
       	// branch 7
        solvebranch
	))



val safeproofu1 =
    safeproofz(easybranchT(unitT))


// This proves the safety of a single, arbitrarily oriented boundary

val singleboundarypf =
     composelistT(
       hpalphaRT*,
       tryruleT(andRight)<(
         composelistT(
       	   hpalphaRT*,
       	   tryruleT(andRight)<(
	     composelistT(
	       tryruleT(seq)*,
	       tryruleT(check),
	       tryruleT(impRight),
	       tryruleT(andLeft),
	       safeproofu1
	     )
,
       	     composelistT(
	       hpalphaRT*,
	       tryruleT(andRight)<(
	         composelistT(
		   hpalphaRT*,
		   tryruleT(andRight)<(
		     composelistT(
                       hpalphaRT*,
		       tryruleT(andRight)<(
                         composelistT(
		           hpalphaRT*,
		           tryruleT(andRight)<(
                             composelistT(
                               hpalphaRT*,
		               tryruleT(andRight)<(
			         composelistT(
                                   hpalphaRT*,
                                   tryruleT(andRight)<(
                                     composelistT(
                                       hpalphaRT*,
                                       tryruleT(andRight)<(
                                         safeproofu1
,
                                         safeproofu1
)),
                                     safeproofu1
)),
			         safeproofu1
)),
			     safeproofu1
)),
			 safeproofu1
)),
		     safeproofu1
)),
		 safeproofu1
)))),
	 composelistT(
	   tryruleT(seq)*,
	   tryruleT(check),
	   tryruleT(impRight),
	   tryruleT(andLeft),
	   safeproofu1
         )
))



val main =
   // outer loop
   tryruleT(loopInduction(loopInvOuter))<(
     // outer loop base case
     tryruleT(andRight)<(
       easiestT,
       composelistT(
         tryruleT(seq)*,
         tryruleatT(renameAssign("ii"))(LeftP(7)),
         tryruleatT(renameAssign("ii"))(RightP(0)),
	 nonarithcloseT
       )
     ),
     composelistT(
        tryruleT(andLeft)*,
        tryruleT(seq)*,
        tryruleT(assignAnyRight)*,
        tryruleatT(assign)(RightP(0)),
        tryruleatT(assign)(RightP(0)),
      	tryruleatT(reorder)(LeftP(8)),
        newestT("fzp",
           fzp_string =>
          newestT("fyp",
             fyp_string =>
              newestT("fxp",
                 fxp_string =>
                 unifyT(parseFormula("GG = 1"),
		    Prover.substitute_Formula("FZP", Fn(fzp_string, Nil),
  		      Prover.substitute_Formula("FYP", Fn(fyp_string, Nil),
      	                 Prover.substitute_Formula("FXP", Fn(fxp_string, Nil),
      	                    loopInvInner))),
      	        (y => unifyT(parseFormula("ZZ = first()"),
                       y,
      	              (x => tryruleT(loopInduction(x)))))))))<(
// nilT, // get rid of me -- scaffolding
// /////
// composelistT(
//   tryruleT(andLeft)*,
//   singleboundarypf,
//   nilT
// ),
// /////
// nilT // get rid of me -- scaffolding

 // inner loop base case
 tryruleT(andRight)<(
   tryruleT(andRight)<(
     tryruleT(andRight)<(
       tryruleT(andRight)<(
         composelistT(
            easiestT,
	    substT*,
	    tryruleatT(hide)(LeftP(8)),
	    tryruleatT(hide)(LeftP(7)),
	    tryruleatT(hide)(LeftP(6)),
	    tryruleatT(hide)(LeftP(5)),
	    tryruleatT(hide)(LeftP(4)),
	    arithT
	 ),
	 identiboxT
       ),
       composelistT(
         tryruleatT(hide)(LeftP(9)),
         tryruleatT(hide)(LeftP(8)),
         tryruleatT(hide)(LeftP(7)),
         tryruleatT(hide)(LeftP(6)),
         tryruleatT(hide)(LeftP(5)),
         substT*,
         arithT
       )
     ),
     identiboxT
   ),
   composelistT(
     tryruleT(impRight),
     tryruleatT(hide)(LeftP(8)),
     cutT(StandardCut,parseFormula("ZZ=first()"),
          parseFormula("first()/=first()"))<(
       composelistT(substT*,easiestT),
 	easiestT
     )
   )
 ),
 // inner loop inductive step
 composelistT(
   tryruleT(andLeft)*,
   singleboundarypf,
   nilT
 ),
 // inner loop postcondition
  composelistT(
    tryruleT(andLeft)*,
    tryruleatT(hide)(LeftP(6)),
    tryruleT(seq)*,
    tryruleT(check)*,
    tryruleT(impRight),
    tryruleatT(assign)(RightP(0)),
    diffsolveT(RightP(0), Endpoint),
    cutT(StandardCut, parseFormula("AA = end()"),
         parseFormula("AA = first() | AA /= first()"))<(
 	composelistT(
 	  tryruleT(orRight),
 	  tryruleT(notEquals),
 	  tryruleT(not),
 	  nonarithcloseT),
 	composelistT(
 	  tryruleT(assign),
 	  tryruleatT(assign)(RightP(0)),
 	  tryruleT(andRight)<(
 	    easiestT,
 	    tryruleT(orLeft)<(
 	      composelistT(
 	         tryruleatT(hide)(LeftP(12)),
 	         tryruleatT(hide)(LeftP(11)),
 		 tryruleT(seq)*,
 		 tryruleT(assign),
 	         substT*,
 		 tryruleatT(reorder)(LeftP(12)),
 		 unifyT(parseFormula("ZZ = end()"),
 		     parseFormula("ZZ = end() & next(end()) = end()"),
 		 m_string => 
 	             tryruleT(loopInduction(m_string)))<(
 		       easiestT,
 		       composelistT(
 		         tryruleT(andLeft),
 			 tryruleT(assign),
 			 tryruleT(andRight)<(
 			   composelistT(
 			     substT*,nonarithcloseT
 			   ),
 			   nonarithcloseT
 			 )
 		       ),
 		       composelistT(
 		         tryruleT(andLeft),
 			 tryruleT(impRight),
 			 substT*,
 			 nonarithcloseT
 		       )
 	             )
 	       ),
 	       composelistT(
 	         tryruleT(impLeft)<(
 		   composelistT(
 		     tryruleT(allLeft(Fn("s",List()))),
 		     tryruleT(impLeft)<(
 		       composelistT(
 		         tryruleatT(hide)(LeftP(14)),
 		         substT*,
 			 tryruleT(seq)*,
 			 tryruleatT(assign)(RightP(0)),
 			 rearrangepf
 		       ),
 		       composelistT(
 		         tryruleatT(hide)(RightP(1)),
 			 substT*,
// 			 tryruleatT(hide)(LeftP(13)),
 			 tryruleatT(hide)(LeftP(12)),
 			 tryruleatT(hide)(LeftP(11)),
 			 tryruleatT(hide)(LeftP(10)),
 			 tryruleatT(hide)(LeftP(9)),
 			 tryruleatT(hide)(LeftP(8)),
 			 tryruleatT(hide)(LeftP(7)),
 			 tryruleatT(hide)(LeftP(6)),
 			 tryruleatT(hide)(LeftP(5)),
 			 tryruleatT(hide)(LeftP(4)),
 			 tryruleatT(hide)(LeftP(3)),
 			 tryruleatT(hide)(LeftP(0)),
 			 tryruleT(andRight)<(arithT,arithT)
 		       )
 		     )
 		   ),
 		   composelistT(
 		     tryruleatT(hide)(RightP(1)),
 		     nonarithcloseT
 		   )
 		 )
 	       )
 	      )
 	    )
 	  )
    )
 )
       ) // end of inner loop
     ),
     // outer loop invariant implies postcondition
     composelistT(
       tryruleT(andLeft)*,
       tryruleT(seq)*,
       tryruleatT(renameAssign("ii"))(LeftP(7)),
       tryruleatT(renameAssign("ii"))(RightP(0)),
       nonarithcloseT
     )
   )


}

