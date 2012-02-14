object Script {

val loopInv =
 parseFormula("K() > 0 & e() > 0 & nx()^2 + ny()^2 = 1 & (qx() - px()) * nx() + (qy() - py()) * ny() >=0")

val main =
   tryruleT(loopInduction(loopInv))<(
     easiestT,
     easiestT,
     easiestT
   )

}
