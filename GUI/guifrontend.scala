package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

//import scala.swing._
import javax.swing._
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

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















import java.net.URL
import java.io.IOException
import java.awt.Dimension
import java.awt.GridLayout


class TreeDemo extends JPanel(new GridLayout(1,0)) with TreeSelectionListener {
    var  htmlPane :JEditorPane = null 
    var tree : JTree = null

        //Create the nodes.
  val top :DefaultMutableTreeNode =
    new DefaultMutableTreeNode("The Java Series")
  createNodes(top)

  //Create a tree that allows one selection at a time.
  tree = new JTree(top)
  tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)

  //Listen for when the selection changes.
  tree.addTreeSelectionListener(this)


  //Create the scroll pane and add the tree to it. 
  val treeView = new JScrollPane(tree)
  
  //Create the HTML viewing pane.
  htmlPane = new JEditorPane()
  htmlPane.setEditable(false)
  initHelp()
  val htmlView = new JScrollPane(htmlPane);

  //Add the scroll panes to a split pane.
  val splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT)
  splitPane.setTopComponent(treeView)
  splitPane.setBottomComponent(htmlView)

  override val minimumSize = new Dimension(100, 50)
  htmlView.setMinimumSize(minimumSize)
  treeView.setMinimumSize(minimumSize)
  splitPane.setDividerLocation(100)
  splitPane.setPreferredSize(new Dimension(500, 300))

  //Add the split pane to this panel.
  add(splitPane)


    /** Required by TreeSelectionListener interface. */
    def valueChanged(e: TreeSelectionEvent) : Unit = {
        val node  = tree.getLastSelectedPathComponent()

    }

    class BookInfo(book : String, filename: String)  {
        val bookName = book
        val bookURL = getClass().getResource(filename)

        override def toString : String = {
            bookName
        }
    }

    def initHelp() : Unit = {
        val s = "TreeDemoHelp.html"
        val helpURL = getClass().getResource(s)
        if (helpURL == null) {
            System.err.println("Couldn't open help file: " + s)
        } 
        displayURL(helpURL)
    }

    def displayURL(url: URL): Unit = {
        try {
            if (url != null) {
                htmlPane.setPage(url)
            } else { //null url
		htmlPane.setText("File Not Found")

            }
        } catch {
          case (e: IOException) => 
            System.err.println("Attempted to read a bad URL: " + url)
        }
    }

    def createNodes( top :DefaultMutableTreeNode): Unit = {
        var category : DefaultMutableTreeNode  = null
        var book : DefaultMutableTreeNode = null;

        category = new DefaultMutableTreeNode("Books for Java Programmers")
        top.add(category)

        //original Tutorial
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Tutorial: A Short Course on the Basics",
            "tutorial.html"))
        category.add(book)

        //Tutorial Continued
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Tutorial Continued: The Rest of the JDK",
            "tutorialcont.html"));
        category.add(book);

        //JFC Swing Tutorial
        book = new DefaultMutableTreeNode(new BookInfo
            ("The JFC Swing Tutorial: A Guide to Constructing GUIs",
            "swingtutorial.html"));
        category.add(book);

        //Bloch
        book = new DefaultMutableTreeNode(new BookInfo
            ("Effective Java Programming Language Guide",
	     "bloch.html"));
        category.add(book);

        //Arnold/Gosling
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Programming Language", "arnold.html"));
        category.add(book);

        //Chan
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Developers Almanac",
             "chan.html"));
        category.add(book);

        category = new DefaultMutableTreeNode("Books for Java Implementers");
        top.add(category);

        //VM
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Virtual Machine Specification",
             "vm.html"));
        category.add(book);

        //Language Spec
        book = new DefaultMutableTreeNode(new BookInfo
            ("The Java Language Specification",
             "jls.html"));
        category.add(book);


        book = new DefaultMutableTreeNode(new BookInfo
            ("I ADDED THIS!!!!11!!!",
             "jls.html"));
        category.add(book);
    }
        

}



object FE {

  def createAndShowGUI : Unit =  {

    //Create and set up the window.
    val frame = new JFrame("PROVER")
    frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)

    //Add content to the window.
    frame.add(new TreeDemo())

    //Display the window.
    frame.pack()
    frame.setVisible(true)
  }



  def start : Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      def run() {
        createAndShowGUI
      }
    });    
  }


  def start1(fa: Actor) : FrontEnd = {
    val w = new FrontEnd(fa)
           
    w.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    w.setSize(800, 640)
//    w.centerOnScreen
    w.setVisible(true)
    println(w)
    w

  }

}
