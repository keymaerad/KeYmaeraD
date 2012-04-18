package KeYmaeraD.Testing

import scala.actors.Actor
import scala.actors.Actor._


// copied this stuff from frontend.scala...
object Examples {
  import KeYmaeraD._
  import KeYmaeraD.Tactics._


  val opts = new org.apache.commons.cli.Options();
  opts.addOption("workers", true, "number of worker subproceses")

  val message = "options:\n-workers"

  var frontactor : KeYmaeraD.FrontActor = null;

  def main(args: Array[String]) : Unit = {
    println("worker says: hello world.")

    frontactor = new KeYmaeraD.FrontActor(None);
    println ("KeYmaeraD frontend loaded.")
    frontactor.start()

    val parser = new org.apache.commons.cli.GnuParser();

    var workers = 1;

    try {
      val cmd = parser.parse(opts, args, false)

      if (!cmd.hasOption("workers")) {
        workers = Runtime.getRuntime().availableProcessors();
      } else {
        workers = java.lang.Integer.parseInt(cmd.getOptionValue("workers", "1"))
      }
    } catch {
      case e: org.apache.commons.cli.UnrecognizedOptionException =>
        println("\nGot a bad option.")
        println(message)
    }

    println("Starting " + workers + " workers.")
    if (workers > 0) dl('findworkers, workers);

    dl('load, "examples/simple.dl")
    dl('tactic, easiestT)

    Thread.sleep(1000)

    dl('quit)
  }

  def dl(cmd: Symbol): Unit = {
    frontactor !? cmd
  }

  def dl(cmd: Symbol, arg: Any): Unit = {
    frontactor.!?((cmd,arg))
  }

  def dl(cmd: Symbol, arg1: Any, arg2: Any): Unit = {
    frontactor.!?((cmd,arg1,arg2))
  }


  def dl(cmd: Symbol, arg1: Any, arg2: Any, arg3 : Any): Unit = {
    frontactor.!?((cmd,arg1,arg2,arg3))
  }


}
