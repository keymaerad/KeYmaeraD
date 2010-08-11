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

  graph.setCellsEditable(false)
  graph.setCellsMovable(false)
  graph.setCellsCloneable(false)
  graph.getModel().beginUpdate()
  try{
    val v1 = graph.insertVertex(gparent, null, "Hello", 20, 20, 80, 30)
    val v2 = graph.insertVertex(gparent, null, "World!", 240, 150, 80, 30)
    graph.insertEdge(gparent, null, "Edge", v1, v2)
  }
  finally
  {
    graph.getModel().endUpdate()
  }
		

  final val  graphComponent : mxGraphComponent = new mxGraphComponent(graph)
  getContentPane().add(graphComponent)




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


