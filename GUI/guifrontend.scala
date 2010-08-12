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

import DLBanyan.Nodes._

class FrontEnd(fa: Actor) extends JFrame("PROVER")  {
  
  val frontactor = fa
//  fa ! 'registergui

  final val graph : mxGraph = new mxGraph()
  val gparent : Object  = graph.getDefaultParent()


  graph.setCellsEditable(false)
  graph.setCellsMovable(false)
  graph.setCellsCloneable(false)
  graph.setConnectableEdges(false)

  graph.getModel().beginUpdate()
  try{
    val v1 = graph.insertVertex(gparent, null, "Hello", 0, 0, 80, 30)
    val v2 = graph.insertVertex(gparent, null, "World!", 0, 0, 80, 30)
    val v3 = graph.insertVertex(gparent, null, "kthxbye", 0, 0, 70, 20)
    val v4 = graph.insertVertex(gparent, null, "?", 0, 0, 60, 20)
    val v5 = graph.insertVertex(gparent, null, "5", 0, 0, 50, 20)
    val v6 = graph.insertVertex(gparent, null, "6", 0, 0, 50, 20)
    val v7 = graph.insertVertex(gparent, null, "7", 0, 0, 50, 20)
    graph.insertEdge(gparent, null, "Edge", v1, v2)
    graph.insertEdge(gparent, null, "Edge2", v1, v3)
    graph.insertEdge(gparent, null, "Edge3", v1, v4)
    graph.insertEdge(gparent, null, "Edge4", v2, v5)
    graph.insertEdge(gparent, null, null, v5, v6)
    graph.insertEdge(gparent, null, null, v6, v7)
//val glayout = new com.mxgraph.layout.hierarchical.mxHierarchicalLayout(graph)
    val glayout = new hierarchical.mxHierarchicalLayout(graph)
    glayout.execute(gparent)
//    val lm = new mxLayoutManager(graph) { 
//      val layout = new mxCompactTreeLayout(graph)
//      override def getLayout(parent :Object) : mxIGraphLayout = { 
//        if (graph.getModel().getChildCount(parent) > 0) 
//           return layout 
//        else return null
//      }
//
//   }
//    lm.executeLayout
  }
  finally
  {
    graph.getModel().endUpdate()
  }
		

  final val  graphComponent : mxGraphComponent = new mxGraphComponent(graph)
  getContentPane().add(graphComponent)


  val nodeMap = new scala.collection.mutable.HashMap[NodeID,Object]()

  def addProofNode(nd: ProofNode): Unit = {
    val v = graph.insertVertex(gparent, null, nd.nodeID.toString, 0,0,50,20)
    nodeMap.put(nd.nodeID, v)
//    for(c <- nd.children) {
//      graph.insertEdge(gparent, null, null,)
//    }
  }

  def addEdges(nd: ProofNode): Unit = {
    nodeMap.get(nd.nodeID) match {
      case Some(v) => 
        for(c <- nd.children) {
          nodeMap.get(c) match {
            case Some(v1) => 
              graph.insertEdge(gparent, null, "", v, v1)
            case None => 
          }
        }
      case None => 
    }
  }

  def drawNodes(nt: scala.collection.mutable.HashMap[NodeID, ProofNode]): Unit = {
    nodeMap.clear
    graph.getModel().beginUpdate()
    graph.selectAll()
    graph.clearSelection()

    try{
      for( (ndID, nd) <- nt) {
        addProofNode(nd)
      }
      for( (ndID, nd) <- nt) {
        addEdges(nd)
      }
          
      val glayout = new hierarchical.mxHierarchicalLayout(graph)
      glayout.execute(gparent)
    }
    finally
    {
      graph.getModel().endUpdate()
    }
    
  }


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


  def start(fa: Actor) : FrontEnd = {
    val w = new FrontEnd(fa)
           
    w.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    w.setSize(800, 640)
//    w.centerOnScreen
    w.setVisible(true)
    println(w)
    w

  }

}


