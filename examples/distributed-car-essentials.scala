dl('load, "examples/distributed-car-essentials.dl")

val rl = loopInduction(
  parseFormula(
    "v1()^2-v2()^2<2*b()*(x2()-x1())&x1()<x2()&"+
    "v1()>=0&v2()>=0&aa()>=0&b()>0&ep()>0"))

val cutrl = 
  directedCut(
    parseFormula(
    "2*b()*x2()>2*b()*x1()+(v1()^2-v2()^2)+(aa()+b())*(aa()*s()^2+2*s()*v1())"
//      "x1()+v1()*ep()+aa()*ep()^2*(1/2)<x2()+v2()*ep()+(0-b())*ep()^2*(1/2)"
      ))


val everythingT: Tactic = 
  composeT(
    repeatT(
      eitherlistT(List(hpalphaT, 
                       alphaT, 
                       nonarithcloseT,
                       betaT, 
                       substT))),
    eitherT(nonarithcloseT, hidethencloseT))



val hardbranch = 
  composelistT(List(repeatT(hpalpha1T),
                    usehints0T(RightP(0)),
                    repeatT(hpalpha1T),
                    repeatT(substT),
                    tryruleatT(cutrl)(LeftP(4)),
                    alleasyT
                    
                      ))




val indtct =                           
  composeT(
   repeatT(hpalpha1T),
   branchT(tryruleT(choose),
           List(composelistT(List(repeatT(hpalpha1T),
                                  branchT(tryruleT(choose), 
                                          List(hardbranch, alleasyT)))),
                composelistT(List(repeatT(hpalpha1T),
                                  branchT(tryruleT(choose), 
                                          List(alleasyT, alleasyT))))
              ) ))


    



dl('gotoroot)
dl('tactic,  branchT(tryruleT(rl),
                     List(alleasyT,
                          indtct,
                          alleasyT
                          )))


