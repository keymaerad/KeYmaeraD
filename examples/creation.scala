dl('load, "examples/creation.dl")
val rl = loopInduction(
  parseFormula(
    "forall i : C. forall j : C. " + 
    "(E(i) = 1 & E(j) = 1 &  ~(i = j) ) ==>" + 
     "    (  (x(i) <  x(j) & v(i) <= v(j) & a(i) <= a(j)) "+
    "  | (x(i) >  x(j) & v(i) >= v(j) & a(i) >= a(j)) ) "

))



val indtct = 
  composelistT(
    hpalpha1T*,
    diffsolveT(RightP(0),Endpoint),
    hpalpha1T*,
    instantiate1T(St("C")),
    instantiate1T(St("C")),
    nullarizeT*    
  )

val posttct = 
   (hpalpha1T*) & instantiate1T(St("C")) 
   

  

dl('gotoroot)
dl('tactic,  branchT(tryruleT(rl),
                     List(tryruleatT(close)(RightP(0)),
                          indtct,
                          posttct
                          )))
