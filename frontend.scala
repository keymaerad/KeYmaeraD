package DLBanyan

import scala.actors.Actor
import scala.actors.Actor._



object CommandLine {

  var frontactor = new FrontActor;



//  def begin : Unit = {
  println ("Welcome to DLBanyan.")
  frontactor.start()
//    frontactor ! 'hi
    
//  }

  def ex = "examples/simple.dl"


  def dl(cmd: Symbol): Unit = {
    frontactor !? cmd
  }

  def dl(cmd: Symbol, arg: Any): Unit = {
    frontactor.!?((cmd,arg))
  }

  def dl(cmd: Symbol, arg1: Any, arg2: Any): Unit = {
    frontactor.!?((cmd,arg1,arg2))
  }



  def runworker(port : Int): Unit = {
    val name = port.toString + ".out"
    val pb = 
      new ProcessBuilder("./runworker",
                         "-c", 
                         "localhost",
                         "-cp", "50001", "-p ",  port.toString)
    pb.redirectErrorStream
    val p = pb.start
//    val is = p.getInputStream
    ()
  }


}
