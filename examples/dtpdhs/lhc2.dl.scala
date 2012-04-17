
object Script  {


val loopinv 
  = parseFormula(
    "(A() > 0 & B() > 0 & eps() > 0) & " +
 "((forall i : C. e(i) = 1 ==> v(i) >= 0)&(" +
 "forall f : C. " +
 "forall l : C." +
  "(e(f) = 1 & e(l) = 1 & x(f) <= x(l) &  (~ (f = l)))  ==>" + 
        "(2 * B() * x(l) > 2 *  B() * x(f) + v(f) ^2 - v(l)^2 &" +
  "        x(f) < x(l)       )))")

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
    cuttct<(
      provecut, 
      tryruleT(orLeft)<(
        tryruleT(orLeft)<(
          hardcase, 
          composelistT(nullarizeT*,hidethencloseT)),
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



val orsg2tct = 
 composelistT(
   tryruleT(andLeft)*,
   instantiate1T(St("C")),
   vacuousT*,
   impleftknownT*,
   tryruleT(impLeft)<(
     impsg1,
     tryruleT(andRight)<( 
       tryruleT(andRight) & nonarithcloseT, 
       composelistT(alphaT*, tryruleT(close))))
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
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(easy0, easy1),
      easy2)
  )



val sg1tct = 
  composelistT(
    hidedoublequantT,
    instantiate1T(St("C")),
    impleftknownT*,
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(easycase, easycase),
      orsg2tct)
  )


val uselemma =  tryruleT(impLeft)<( sg1tct,  tryruleT(close))

val precond = 
    tryruleT(andRight)<(
      composelistT(
        tryrulepredT(hide)(fm => fm match { case Atom(R("<=",_)) => false case _ => true}),
        hidethencloseT
      ),
      composelistT(alphaT*,
                   tryruleT(commuteEquals),
                   tryruleT(close)
                 )
    )


val oror0tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    tryruleT(impLeft)<(hidethencloseT,precond)
  )

val oror1tct = 
  composelistT(
    alphaT*,
    nullarizeT*,
    substT*,
    hidethencloseT
  )

val demotactic = 
  cuttct<(
    hideforprovecut & hidethencloseT, 
    hidethencloseT)

val oror2tct = 
  composelistT(
    alphaT*,
    instantiate1T(St("C")),
    vacuousT*,
    nullarizeT*,
    substT*,
    tryruleT(impLeft)<(
      tryruleT(impLeft)<(
        // Put demotactic here.
        hidethencloseT,
        precond
      ),
      precond
    )
    
  )


val or0tct = 
  composelistT(
    alphaT*,
    hideunivsT(St("C")),
    tryruleT(orLeft)<(
      tryruleT(orLeft)<(oror0tct,oror1tct), 
      oror2tct)
  )



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
          tryruleT(orLeft)<(or0tct,or0tct),
          or0tct)

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


val velpos = 
  composelistT(
    hpalphaT*,
    instantiatebyT(St("C"))(
      List(("i",List("i"))))*,
    alleasyT
  )

val tyltct = composelistT(
  hpalphaT*,
  diffsolveT(RightP(0),Endpoint),
  hpalphaT*,
  tryruleT(andRight)<(
    alleasyT,
    tryruleT(andRight)<(
      velpos,
      composelistT(
        hpalphaT*,
        instantiate3T,
        okcuttct<(
          provelemma,
          uselemma
        )
      )
    )
  )
)




val deletetct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      composelistT(
        hpalphaT*,
        (nonarithcloseT | alphaT | betaT)*
      ),
      tryruleT(andRight)<(
        composelistT(
          alphaT*,
          instantiatebyT(St("C"))(List(("i", List("i")),
                                       ("j", List("i"))))*,
          (nonarithcloseT | alphaT | betaT | substT)*
        ),
        composelistT(
          alphaT*,
          instantiatebyT(St("C"))(List(("i", List("f", "l")),
                                       ("j", List("f", "l")),
                                       ("f", List("f")),
                                       ("l", List("l"))))*,
          (nonarithcloseT | alphaT | betaT | substT)*
        )
      )
    )
  )

val createtct = 
  composelistT(
    hpalphaT*,
    tryruleT(andRight)<(
      composelistT(
        hpalphaT*,
        (nonarithcloseT | alphaT | betaT)*
      ),
      tryruleT(andRight)<(
        composelistT(
          alphaT*,
          instantiatebyT(St("C"))(List(("i", List("i")),
                                       ("j", List("i"))))*,
          (nonarithcloseT | alphaT | betaT | substT)*
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
              impleftknownT*,
              tryruleT(andRight)<(
                tryruleT(andRight)<(
                  tryruleT(andRight)<(
                    tryruleatT(impLeft)(LeftP(5))<(
                      ((substT*) & nonarithcloseT),
                      ((alphaT*) & (substT*) &  (tryruleatT(impLeft)(LeftP(1))<(
                        nonarithcloseT,
                        (tryruleT(andRight)) & (alphaT* ) & nonarithcloseT)))
                    ),
                    tryruleatT(impLeft)(LeftP(2))<(
                      ((substT*) & nonarithcloseT),
                      ((alphaT*) & (substT*) &  (tryruleatT(impLeft)(LeftP(3))<(
                        nonarithcloseT,
                        (tryruleT(andRight))<(nonarithcloseT, 
                                              alphaT & tryruleT(commuteEquals) & nonarithcloseT))))
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
  )




val initiallytrue = 
  composelistT(
    (nonarithcloseT | alphaT | betaT)*,
    instantiatebyT(St("C"))(
       List((("i"), List("i", "f", "l"))))*,
    nullarizeT*,
    hidethencloseT
  )



val postcondition = 
  composelistT(
    alphaT*,
    instantiatebyT(St("C"))(
      List(
           (("f"), List("f")),
           (("l"), List("l"))))*,
    (nonarithcloseT | alphaT | betaT)*,
    nullarizeT*,
    hidethencloseT
  )




val wholeproof = 
  composelistT(
    tryruleT(loopInduction(loopinv))<(

      // Invariant is initially true.
      initiallytrue,

      // Induction Step.
      composelistT(
        hpalphaT*,
        tryruleT(andRight)<(
          composelistT(
            tryruleT(choose),
            tryruleT(andRight)<(
              deletetct,
              createtct)
          ),
          tyltct
        )      
      ),
      
      // Invariant implies postcondition.
      postcondition
    )

  )


val main = wholeproof

}
