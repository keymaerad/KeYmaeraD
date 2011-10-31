package KeYmaeraD

import scala.actors.Actor
import scala.actors.Actor._

object CommandLine {

  var frontactor : FrontActor = null;

  def initFrontActor {//repl: scala.tools.nsc.interpreter.ILoop) {
    frontactor = new FrontActor() //(repl);
    println ("KeYmaeraD frontend loaded.")
    frontactor.start()

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
