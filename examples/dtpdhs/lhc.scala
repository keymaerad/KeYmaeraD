dl('load, "examples/dtpdhs/lhc.dl")



val cuttct = cutT(
  DirectedCut,
  parseFormula(
    "2*B()*X1>2*B()*X2+ V2^2 - V1^2 +" + 
     "(A()+B())*(A()*eps()^2+2 * eps()*V2)"
  ),
  parseFormula(
    "2*B()*X1>2*B()*X2+ V2^2 - V1^2 +" + 
     "(A()+B())*(A()*s()^2+2 * s()*V2)"
  )
)



val okcuttct = cutT(
  StandardKeepCut,
  parseFormula(
   "(e(F) = 1 & e(L) = 1 & x(F)<=x(L) & ~F=L )" + 
    "==>(2*B()*x(L)>2*B()*x(F)+v(F)^2-v(L)^2 & x(F) < x(L))"
  ),
  parseFormula(
   "e(F) = 1 & e(L) = 1 & x(F)<=x(L)&~F=L" 
  )
)

  
val mostthingsT = 
    repeatT(
      eitherlistT(hpalphaT, 
                  alphaT, 
                  nonarithcloseT,
                  betaT, 
                  substT))


val everythingT: Tactic = 
  composeT(
    repeatT(
      eitherlistT(hpalphaT, 
                  alphaT, 
                  nonarithcloseT,
                  betaT, 
                  substT)),
    eitherT(nonarithcloseT, hidethencloseT))


val hideforprovecut = 
  composelistT(
   tryruleunifyT(hide) (
     parseFormula( "B * s()  + V >=0")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "2*B()*X2>2*B()*X1 + V1^2-V2^2")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "1/2 * B  * s()^2  + V * s()  + X <= 1/2 * A() * s()^2  + V1 * s() + X1")
   )*
  )


val provecut = 
 composelistT(
   tryrulepredT(hide) (fm => fm match {case Binop(Or,_,_) => true case _ => false}),
   tryrulepredT(hide) (fm => fm match {case Binop(Imp,_,_) => true case _ => false}),
   alphaT*,
   nullarizeT*,
   tryruleunifyT(hide) (
     parseFormula( "X1=1/2*A*s()^2+V*s()+X2")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "V1=A*s()+V")
   )*,
   tryruleunifyT(hide) (
     parseFormula( "2*B()*X2>2*B()*X1 + V1^2-V2^2")
   )*,
   substT*,
   hidethencloseT
 )

val hardcase = 
  composelistT(
    nullarizeT*,
    substT*,
    hidethencloseT
  )


val impsg1 = 
  composelistT(
    branchT(cuttct,
            List(provecut, 
                 branchT(tryruleT(orLeft),
                         List(branchT(tryruleT(orLeft),
                                      List(hardcase, 
                                           composelistT(nullarizeT*,hidethencloseT))),
                              composelistT(
                                tryruleT(andLeft)*,
                                hideunivsT(St("C")),
                                nullarizeT*,
                                substT*,
                                hidethencloseT
                              )
                            )
                       )
               )
          )
  )


val orsg2tct = 
 composelistT(
   tryruleT(andLeft)*,
   instantiate1T(St("C")),
   vacuousT*,
   branchT(tryruleT(impLeft),
           List(impsg1,
                branchT(tryruleT(andRight),List(tryruleT(close), 
                                                composelistT(alphaT*, tryruleT(close))))))
 )


val easy0 = 
  composelistT(
    nullarizeT*,
    substT*,
    hidethencloseT
)

val easy1 = easy0

val easy2 = 
  composelistT(
    alphaT*,
    hideunivsT(St("C")),
    easy0
  )

val easycase = 
  composelistT(
    alphaT*,
    branchT(tryruleT(orLeft),
            List(branchT(tryruleT(orLeft), List(easy0, easy1)),easy2))
  )

val orsg0tct = easycase

val orsg1tct = easycase





val sg1tct = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    branchT(tryruleT(orLeft),
            List(branchT(tryruleT(orLeft), List(orsg0tct, orsg1tct)),orsg2tct))
             )


val uselemma =  branchT(tryruleT(impLeft),
                        List(sg1tct,
                             tryruleT(close)))




val oror1tct = unitT


val precond = 
  branchT(
    tryruleT(andRight),
    List(
      composelistT(
        tryrulepredT(hide)(fm => fm match { case Atom(R("<=",_)) => false case _ => true}),
        hidethencloseT
      ),
      composelistT(alphaT*,
                   tryruleT(commuteEquals),
                   tryruleT(close)
                 )
       )
  )


val oror0tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    branchT(tryruleT(impLeft),
            List(hidethencloseT,precond))
  )

val oror1tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    hidethencloseT
  )

val oror2tct = 
  composelistT(
    alphaT*,
    instantiate1T(St("C")),
    vacuousT*,
    nullarizeT*,
    substT*,
    branchT(tryruleT(impLeft),
            List(
              branchT(tryruleT(impLeft),
                      List( 
                        composelistT(
                          branchT(cuttct,
                                  List(
                                    composelistT(
                                      hideforprovecut,
                                      hidethencloseT
                                    ),
                                    hidethencloseT
                                  ))),
                        precond
                        )
                      ),
              precond
            )
    
          )
  )

val or0tct = 
  composelistT(
    alphaT*,
    hideunivsT(St("C")),
    branchT(tryruleT(orLeft), 
            List(branchT(tryruleT(orLeft),
                         List(oror0tct,oror1tct)), 
                 oror2tct))
  )


val or1tct = 
  composelistT(
    or0tct
  )

val or2tct = 
 composelistT(or0tct)


val andbranch1 = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    alphaT*,
    tryruleT(andRight)<(
      tryruleT(andRight) & tryruleT(close),
      composelistT(
        composelistT(
          impleftknownT*
        ),
        tryruleT(orLeft)<(
          tryruleT(orLeft)<(or0tct,or1tct),
          or2tct)

      )
    )
  )

val provelemma = 
  composelistT(
    tryruleunifyT(hide)(parseFormula("L > A + B - C & X1 < X2")),
    instantiate4T,
    tryruleT(andRight)<(
      andbranch1, 
      composelistT(tryruleT(not), tryruleT(close))
    )
  )


val veltct = new Tactic("veltct"){
  def apply(nd:Nodes.OrNode) = {
    val Sequent(sig, cs, ss) = nd.goal
    ss match {
      case List(Atom(R(">=", List(Fn(v,List(i)), _)))) =>
        tryruleT(allLeft(i))(nd)
      case _ => None
    }
  }
}

val velpos = 
  composelistT(
    hpalpha1T*,
    veltct,
    alphaT*,
    tryruleT(impLeft)<(
      tryruleT(close),
      tryruleT(close)
    )
  )

val tyltct = composelistT(
  hpalpha1T*,
  diffsolveT(RightP(0),Endpoint),
  hpalpha1T*,
  tryruleT(andRight)<(
    velpos,
    composelistT(
      hpalpha1T*,
      instantiate3T,
      okcuttct<(
        provelemma,
        uselemma
      )
    )
  )
)




val deletetct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      composelistT(
        hpalpha1T*,
        instantiate5T(St("C")),
        hideunivsT(St("C")),
        tryruleatT(impLeft)(LeftP(0))<(
          tryruleT(close),
          tryruleatT(impLeft)(LeftP(0))<(
            ((alphaT*) & (substT*) & nonarithcloseT  ),
            ((alphaT*) & (substT*) & nonarithcloseT  )
          )
        )
      ),
      composelistT(
        alphaT*,
        tryruleatT(commuteEquals)(RightP(0)),
        instantiate4T,
        tryruleatT(impLeft)(LeftP(0))<(
          tryruleT(close),
          composelistT(
            instantiate1T(St("C")),
            hideunivsT(St("C")),
            tryruleT(andRight)<(
              tryruleT(andRight)<(
                tryruleT(andRight)<(
                  tryruleatT(impLeft)(LeftP(3))<(
                    ((substT*) & nonarithcloseT),
                    ((alphaT*) & (substT*) & nonarithcloseT  )
                  ),
                  tryruleatT(impLeft)(LeftP(1))<(
                    ((substT*) & nonarithcloseT),
                    ((alphaT*) & (substT*) & nonarithcloseT  )
                  )
                ),
                tryruleT(close)
              ),
              (tryruleT(not) & tryruleT(commuteEquals) & tryruleT(close))
            )
          )
        )
      )
    )
  )




val createtct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      composelistT(
        hpalpha1T*,
        instantiate5T(St("C")),
        hideunivsT(St("C")),
        tryruleatT(impLeft)(LeftP(2))<(
          (substT*)  & (tryruleatT(impLeft)(LeftP(1))   )  & nonarithcloseT ,
          tryruleatT(impLeft)(LeftP(0))<(
            ((alphaT*) & (substT*) & nonarithcloseT  ),
            ((alphaT*) & (substT*) & nonarithcloseT  )
          )
        )
      ),
      composelistT(
        alphaT*,
        tryruleatT(commuteEquals)(RightP(0)),
        instantiate4T,
        tryruleatT(impLeft)(LeftP(0))<(
          tryruleT(close),
          composelistT(
            instantiate1T(St("C")),
            hideunivsT(St("C")),
            tryruleT(andRight)<(
              tryruleT(andRight)<(
                tryruleT(andRight)<(
                  tryruleatT(impLeft)(LeftP(3))<(
                    ((substT*) & nonarithcloseT),
                    ((alphaT*) & (substT*) & nonarithcloseT  )
                  ),
                  tryruleatT(impLeft)(LeftP(1))<(
                    ((substT*) & nonarithcloseT),
                    ((alphaT*) & (substT*) & nonarithcloseT  )
                  )
                ),
                tryruleT(close)
              ),
              (tryruleT(not) & tryruleT(commuteEquals) & tryruleT(close))
            )
          )
        )
      )
    )
  )




val starttct = 
  composelistT(
    hpalpha1T*,
    tryruleT(andRight)<(
      composelistT(
        tryruleT(choose),
        tryruleT(andRight)<(
          deletetct,
          createtct)
      ),
      tyltct
    )      
  )


dl('gotoroot)
dl('tactic, starttct)
