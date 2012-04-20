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



  def testexample(i: IMain, filename : String, allowedtime : Long, script : Array[Any]) : Unit = {
    val problemfile = filename.substring(0, filename.length - 6)
    println("loading " + problemfile)
    dl('load, problemfile)
    
    println("interpreting " + filename)
    interpretfile(i, filename)
    i.interpret("script(0) = Script.main")
    

    dl('tactic, script(0).asInstanceOf[Tactic])

    while (true != (frontactor !? 'rootproved)) {
      println("waiting...")
      Thread.sleep(500)
    }
    println("proved!")

    
  }

  def main(args: Array[String]) : Unit = {
    println("worker says: hello world.")


    val s = new Settings(str => println(str))

//  var i = new ILoop()
    println("starting an interpreter...")
    var i = new IMain() {
      override protected def parentClassLoader: ClassLoader = getClass.getClassLoader()
    }
    var res = Array[Any](nilT)
//  i.settings = s
//  i.settings.embeddedDefaults
//  i.createInterpreter()
  i.interpret("import KeYmaeraD._")
  i.interpret("import KeYmaeraD.P._")
  i.interpret("import KeYmaeraD.Tactics._")
  i.interpret("import KeYmaeraD.Rules._")
  i.interpret("import KeYmaeraD.RulesUtil.RightP")
  i.interpret("import KeYmaeraD.RulesUtil.LeftP")
  i.bind("script", "Array[Any]", res)


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


    while (true != (frontactor !? 'rootproved)) {
      println("waiting...")
      Thread.sleep(500)
    }
      println("proved!")

 

    println("starting other examples")
    testexample(i, "examples/aircraft/big_disc.dl.scala", 1000, res)
    testexample(i, "examples/aircraft/two_tiny_discs.dl.scala", 1000, res)
//    println("res(0) = " + res(0))



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
