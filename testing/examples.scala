package KeYmaeraD.Testing

import scala.actors.Actor
import scala.actors.Actor._

import scala.tools.nsc.interpreter._
import scala.tools.nsc.Settings

import KeYmaeraD.Tactics._

// copied this stuff from frontend.scala...
object Examples {
  import KeYmaeraD._
  import KeYmaeraD.Tactics._


  val opts = new org.apache.commons.cli.Options();
  opts.addOption("workers", true, "number of worker subproceses")

  val message = "options:\n-workers"

  var frontactor : KeYmaeraD.FrontActor = null;


  def interpretfile(i : IMain, filename : String) {
      val fi = 
        new java.io.FileInputStream(filename)
     val br = new java.io.BufferedReader(new java.io.InputStreamReader(fi))
     var ins1 = ""
     var ln = br.readLine()
     while (ln != null){
       ins1 = ins1 + ln + "\n"
       ln = br.readLine()
     }
    
    i.interpret(ins1)

  }



  def testexample(filename : String, allowedtime : Long) : Unit = {
    dl('load, filename)
    
    
  }

  def main(args: Array[String]) : Unit = {
    println("worker says: hello world.")


  val s = new Settings(str => println(str))

//  var i = new ILoop()
  var i = new IMain()
  var res = Array[Tactic](nilT)
//  i.settings = s
//  i.settings.embeddedDefaults
//  i.createInterpreter()
  i.interpret("import KeYmaeraD._")
  i.interpret("import KeYmaeraD.P._")
  i.interpret("import KeYmaeraD.Tactics._")
  i.interpret("import KeYmaeraD.Rules._")
  i.interpret("import KeYmaeraD.RulesUtil.RightP")
  i.interpret("import KeYmaeraD.RulesUtil.LeftP")
  i.interpret("val x = 4 \n val r = 5")
  i.bind("result", "Array[KeYmaeraD.Tactics.Tactic]", res)
  i.interpret("println(result)")
  interpretfile(i, "examples/aircraft/big_disc.dl.scala")
  i.interpret("result(0) = Script.main")
  
    
//  val pf = new scala.tools.nsc.io.PlainFile("examples/aircraft/big_disc.dl.scala")
//    val bf = new scala.tools.nsc.util.BatchSourceFile(pf)
//  i.compileSources(bf)

  println("res(0) = " + res(0))

//  i.interpretAllFrom(scala.tools.nsc.io.File("examples/creation.scala"))
  println("done")

  System.exit(0) 


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
