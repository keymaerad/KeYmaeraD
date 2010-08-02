
import DLBanyan.FrontEnd._
dl('load, "examples/simple.dl")
dl('here)

dl('apply, DLBanyan.Rules.Right(0), "seq")
 dl('goto, 3)

dl('here)

dl('apply, DLBanyan.Rules.Right(0), "assignRight")

 dl('goto, 5)
 dl('here)

 dl('apply, DLBanyan.Rules.Right(0), "chooseRight")
 dl('goto, 7)
dl('here)
dl('apply, DLBanyan.Rules.Right(0), "assignRight")

dl('here)

 dl('goto, 9)
dl('goto, 10)


dl('here)
dl('job, "ch")
