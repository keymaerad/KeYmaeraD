object Script {

val main =
  composelistT(
    tryruleT(seq)*,
    substT*,
    nonarithcloseT
  )

}
