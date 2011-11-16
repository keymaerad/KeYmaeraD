package KeYmaeraD

import scala.actors.Actor
import scala.actors.Actor._

object CommandLine {

  val opts = new org.apache.commons.cli.Options();
  opts.addOption("workers", true, "number of worker subproceses")
  opts.addOption("nogui", /* hasArg = */ false, "turn gui off")


  var frontactor : FrontActor = null;

  def initFrontActor (args : Array[String],
                      repl: scala.tools.nsc.interpreter.ILoop) {
    frontactor = new FrontActor(repl);
    println ("KeYmaeraD frontend loaded.")
    frontactor.start()

    val parser = new org.apache.commons.cli.GnuParser();
    val cmd = parser.parse(opts, args)

    if (!cmd.hasOption("nogui")) {
      dl('gui)
    }

    var workers = 1;
    if (!cmd.hasOption("workers")) {
      workers = Runtime.getRuntime().availableProcessors();
    } else {
      workers = java.lang.Integer.parseInt(cmd.getOptionValue("workers", "1"))
    }
    println("Starting " + workers + " workers.")
    if (workers > 0) dl('findworkers, workers);

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
