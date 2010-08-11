package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

//import scala.swing._
import javax.swing._

import com.mxgraph.swing.mxGraphComponent
import com.mxgraph.view._
import com.mxgraph.layout._

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
  graph.setConnectableEdges(false)
  graph.getModel().beginUpdate()
  try{
    val v1 = graph.insertVertex(gparent, null, "Hello", 20, 20, 80, 30)
    val v2 = graph.insertVertex(gparent, null, "World!", 240, 150, 80, 30)
    val v3 = graph.insertVertex(gparent, null, "kthxbye", 220, 300, 70, 20)
    val v4 = graph.insertVertex(gparent, null, "?", 400, 160, 60, 20)
    graph.insertEdge(gparent, null, "Edge", v1, v2)
    graph.insertEdge(gparent, null, "Edge2", v1, v3)
    graph.insertEdge(gparent, null, "Edge3", v1, v4)
    val lm = new mxLayoutManager(graph) { 
      val layout = new mxCompactTreeLayout(graph)
      override def getLayout(parent :Object) : mxIGraphLayout = { 
        if (graph.getModel().getChildCount(parent) > 0) 
           return layout 
        else return null
      }

    }
  }
  finally
  {
    graph.getModel().endUpdate()
  }
		
  val glayout = new mxCircleLayout(graph)
  glayout.execute(gparent)


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


