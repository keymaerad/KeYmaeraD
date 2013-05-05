object Script {

val main =
  composelistT(
    tryruleT(seq)*,
    tryruleatT(commuteEquals)(LeftP(0)),
    substT,
    substT,
    nonarithcloseT
  )

}
