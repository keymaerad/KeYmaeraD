import DLBanyan.CommandLine._
import DLBanyan.Rules._
import DLBanyan.RulesUtil.RightP
import DLBanyan.RulesUtil.LeftP
import DLBanyan.Tactics._
import DLBanyan.P._

import DLBanyan._

:load _loader.scala

dl('load, "examples/simple.dl")
dl('gui)

 print("Starting workers")
var workers = 0 //Runtime.getRuntime().availableProcessors()
if (args.length > 0)
   workers = java.lang.Integer.parseInt(args(0))
if (workers > 0)
	dl('findworkers, workers)


