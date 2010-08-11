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


  def gui : Unit = {
    DLBanyan.GUI.FE.main
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




}
