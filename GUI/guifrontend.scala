package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

//import scala.swing._
import javax.swing._

import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;


class FrontEnd extends JFrame("PROVER")  {
  
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


  def main : Unit = {
    val w = new FrontEnd 
           
    w.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    w.setSize(840, 600)
//    w.centerOnScreen
    w.setVisible(true)
    println(w)

  }

}


