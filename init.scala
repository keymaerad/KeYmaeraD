
import DLBanyan.CommandLine._
import DLBanyan.Rules._
import DLBanyan.RulesUtil.RightP
import DLBanyan.RulesUtil.LeftP
import DLBanyan.Tactics._
import DLBanyan.P._

import DLBanyan._


dl('load, "examples/simple.dl")
dl('gui)

dl('findworkers, Runtime.getRuntime().availableProcessors())
/* TODO Where to put the following code so that it's actually executed?
def main(args: Array[String]) : Unit = {
	var workers = Runtime.getRuntime().availableProcessors()
	if (args.length > 0)
	    workers = java.lang.Integer.parseInt(args(0))
	if (workers > 0)
	    dl('findworkers, workers)
}
*/