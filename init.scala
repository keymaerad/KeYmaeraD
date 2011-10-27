import KeYmaeraD.CommandLine._
import KeYmaeraD.Rules._
import KeYmaeraD.RulesUtil.RightP
import KeYmaeraD.RulesUtil.LeftP
import KeYmaeraD.Tactics._
import KeYmaeraD.P._

import KeYmaeraD._

:load _args.scala

dl('load, "examples/simple.dl")
dl('gui)

 print("Starting workers")
var workers = Runtime.getRuntime().availableProcessors()
if (args.length > 0)
   workers = java.lang.Integer.parseInt(args(0))
if (workers > 0)
	dl('findworkers, workers)

//println("Starting power Scala power mode...")
//:power

