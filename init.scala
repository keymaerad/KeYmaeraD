import KeYmaeraD.CommandLine._
import KeYmaeraD.Rules._
import KeYmaeraD.RulesUtil.RightP
import KeYmaeraD.RulesUtil.LeftP
import KeYmaeraD.Tactics._
import KeYmaeraD.P._
import KeYmaeraD._
:load _args.scala

initFrontActor(args, repl)

dl('load, "examples/simple.dl")

