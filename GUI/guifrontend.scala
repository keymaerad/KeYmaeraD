package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

//import scala.swing._
import javax.swing._

import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import scala.actors.Actor
import scala.actors.Actor._

class FrontEnd(fa: Actor) extends JFrame("PROVER")  {
  
  val frontactor = fa
  fa ! 'registergui

  final val graph : mxGraph = new mxGraph()
  val gparent : Object  = graph.getDefaultParent()

  def test : Unit = {
    println("hello world")
  }

/*
  override def closeOperation() : Unit = {
    System.exit(0)
  }
*/

}



object FE {


  def start(fa: Actor) : Unit = {
    val w = new FrontEnd(fa)
           
    w.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    w.setSize(840, 600)
//    w.centerOnScreen
    w.setVisible(true)
    println(w)

  }

}


