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


import java.net.URL
import java.io.IOException
import java.awt.Dimension
import java.awt.GridLayout


class TreeModel extends javax.swing.tree.TreeModel {
  import javax.swing.event.TreeModelEvent
  import javax.swing.event.TreeModelListener

  import DLBanyan.Nodes._

  val treeModelListeners =  new scala.collection.mutable.HashSet[TreeModelListener]()

  def addTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.add(l)
  }

  def removeTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.remove(l)
  }

//  def fireEvent(e: 


  def getIndexOfChild(parent: Any, child: Any): Int = (parent,child) match {
    case (p: ProofNode, c: ProofNode) =>
      p.children.indexOf(c.nodeID)
    case _ => 
      0
  }

  def getChild(parent: Any, index: Int): Object = parent match {
    case (pn: ProofNode) =>
      getnode(pn.children(index))
    case _ => 
      null
  }

  def getChildCount(parent: Any): Int = parent match {
    case (pn: ProofNode) =>
      pn.children.length
    case _ => 
      0
  }
  
  def getRoot(): Object = {
    rootNode
  }

  def isLeaf(node: Any): Boolean = node match {
    case (pn: ProofNode) =>
      pn.children.isEmpty
    case _ => 
      true
  }
  

  // I think this would get used if the user could make changes
  // through the gui.
  def valueForPathChanged(path: javax.swing.tree.TreePath, newValue: Any): Unit = {
    ()
  }

}



class FrontEnd(fa: Actor) 
  extends JPanel(new GridLayout(1,0)) with TreeSelectionListener {

    val frontactor = fa

    var  htmlPane :JEditorPane = null 
    var tree : JTree = null

        //Create the nodes.
  val top :DefaultMutableTreeNode =
    new DefaultMutableTreeNode("The Java Series")
  createNodes(top)

  //Create a tree that allows one selection at a time.
//  tree = new JTree(top)

  val tm = new TreeModel()
  tree = new JTree(tm)
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
  val splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT)
  splitPane.setTopComponent(treeView)
  splitPane.setBottomComponent(htmlView)

  override val minimumSize = new Dimension(100, 50)
  htmlView.setMinimumSize(minimumSize)
  treeView.setMinimumSize(minimumSize)
  splitPane.setDividerLocation(300)
  splitPane.setPreferredSize(new Dimension(800, 640))

  //Add the split pane to this panel.
  add(splitPane)


    /** Required by TreeSelectionListener interface. */
    def valueChanged(e: TreeSelectionEvent) : Unit = {
        val node : ProofNode = 
          tree.getLastSelectedPathComponent() match {
            case (nd : ProofNode) => nd
            case _ => null
          }

      htmlPane.setText(node.toPrettyString)
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

    def displayProofNode(nd: ProofNode): Unit = {
        try {
          htmlPane.setText(nd.toPrettyString)
        } catch {
          case (e: IOException) => 
            System.err.println("could not display proof node")
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

  def drawNodes(nt: scala.collection.mutable.HashMap[NodeID, ProofNode]): Unit = {
    top.removeAllChildren()

    /*
      for( (ndID, nd) <- nt) {
        addProofNode(nd)
      }
      for( (ndID, nd) <- nt) {
        addEdges(nd)
      }
      */    
  }



/*
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
        
*/
}



object FE {

  def createAndShowGUI(fa: Actor) : Unit =  {

    //Create and set up the window.
    val frame = new JFrame("PROVER")
    frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)

    //Add content to the window.
    frame.add(new FrontEnd(fa))

    //Display the window.
    frame.pack()
    frame.setVisible(true)
  }



  def start(fa: Actor) : Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      def run() {
        createAndShowGUI(fa)
      }
    });    
  }

  


}
