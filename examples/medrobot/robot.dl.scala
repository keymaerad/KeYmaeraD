object Script {

val loopInv =
 parseFormula("K() > 0 & e() > 0 & qy() >= 0")

val main =
   tryruleT(loopInduction(loopInv))<(
     nilT,
     nilT,
     nilT
   )

}
