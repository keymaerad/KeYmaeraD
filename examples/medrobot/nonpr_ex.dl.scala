object Script {

val main =
  composelistT(
    tryruleT(seq)*,
    tryruleatT(renameAssign("ii"))(LeftP(0)),
    tryruleatT(renameAssign("ii"))(RightP(0)),
    nonarithcloseT
  )

}
