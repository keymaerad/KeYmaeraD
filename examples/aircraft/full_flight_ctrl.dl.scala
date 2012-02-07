object Script {

val loopinv = 
  parseFormula (
   "((forall i : C ." +
         "forall j : C ."+
            "(disc1(i) - disc1(j))^2 + (disc2(i) - disc2(j))^2 >= (4*minr() + protectedzone())^2) "+
      "& (forall i : C . (c1(i) -x1(i))^2 + (c2(i) - x2(i))^2 = minr()^2)" +
      "& (forall i : C . (c1(i) - disc1(i))^2 + (c2(i) - disc2(i))^2 = minr()^2))")


val starttct =
   tryruleT(loopInduction(loopinv))

val main = starttct

}
