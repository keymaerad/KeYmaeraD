package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

//import scala.swing._
import javax.swing._
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

import scala.actors.Actor
import scala.actors.Actor._

import DLBanyan.Nodes._


import java.net.URL
import java.io.IOException
import java.awt.Dimension
import java.awt.GridLayout


class TreeModel(fe: FrontEnd) extends javax.swing.tree.TreeModel {
  import javax.swing.event.TreeModelEvent
  import javax.swing.event.TreeModelListener

  

  import DLBanyan.Nodes._

  val frontend = fe

  val treeModelListeners =  
    new scala.collection.mutable.HashSet[TreeModelListener]()

  def addTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.add(l)
  }

  def removeTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.remove(l)
  }


  def fireNodesInserted(pt: ProofNode, newnds: List[ProofNode]): Unit = {
    val path = getPath(pt)
//    println("path = " + path)
    val c: Array[Object] = newnds.toArray
    val newlength = pt.getchildren.length 
    val oldlength = newlength - newnds.length
    val ci: Array[Int] = Range(oldlength, newlength).toArray
    val e = new TreeModelEvent(this,path,ci,c)
    for(l <- treeModelListeners){
      l.treeNodesInserted(e)
//      l.treeStructureChanged(e)
    }
    
    frontend.fireNodesInserted(path)
    

  }

  def fireChanged(nd: ProofNode): Unit = {
    val path = getPath(nd)
    val e = new TreeModelEvent(this,path)
    for(l <- treeModelListeners){
      l.treeNodesChanged(e)
    }

  }

  def fireNewRoot(nd: ProofNode): Unit = {
    val path:Array[Object] = List(nd).toArray
    val e = new TreeModelEvent(this, path)
    for(l <- treeModelListeners){
      l.treeStructureChanged(e)
    }

  }


  def getPathAux(nd: ProofNode): List[Object] = nd.parent match {
    case None =>
      if (nd == rootNode) {
        List(nd)
      } else {
        throw new Error("path did not lead to rootNode")
      }
    case Some(pt) =>
      val ptnd = getnode(pt)
      nd :: getPathAux(ptnd)
  }

  def getPath(nd: ProofNode): Array[Object] = {
    val p = getPathAux(nd)
    p.reverse.toArray
  }


  def getIndexOfChild(parent: Any, child: Any): Int = (parent,child) match {
    case (p: ProofNode, c: ProofNode) =>
      p.getchildren.indexOf(c.nodeID)
    case _ => 
      0
  }

  def getChild(parent: Any, index: Int): Object = parent match {
    case (pn: ProofNode) =>
      val r = getnode(pn.getchildren.apply(index))
//      println("getting child  " + index + " of " + pn)
//      println("it is " + r)
      r
    case _ => 
      null
  }

  def getChildCount(parent: Any): Int = parent match {
    case (pn: ProofNode) =>
      val r = pn.getchildren.length
//      println("getting child count of " + pn)
//      println("it is " + r)
      r
    case _ => 
      0
  }
  
  def getRoot(): Object = {
    rootNode
  }

  def isLeaf(node: Any): Boolean = node match {
    case (pn: ProofNode) =>
      pn.getchildren.isEmpty
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

    import javax.swing.tree.DefaultTreeCellRenderer
    import java.awt.Component

    val frontactor = fa


    var  htmlPane :JEditorPane = null 
    var tree : JTree = null


  val tm = new TreeModel(this)
  fa ! ('registergui, tm)

  tree = new JTree(tm)
  tree.setCellRenderer(new MyRenderer)
  tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)

  //Listen for when the selection changes.
  tree.addTreeSelectionListener(this)


  //Create the scroll pane and add the tree to it. 
  val treeView = new JScrollPane(tree)
  
  //Create the HTML viewing pane.
  htmlPane = new JEditorPane()
  htmlPane.setEditable(false)
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
          tree.getLastSelectedPathComponent() match {
            case (nd : ProofNode) => 
              htmlPane.setText(nd.toPrettyString)
            case _ => null
          }

    }


    def fireNodesInserted(path: Array[Object]): Unit = {
      val tpath = new javax.swing.tree.TreePath(path)
      tree.expandPath(tpath)
    }



    class MyRenderer extends DefaultTreeCellRenderer {

      override def getTreeCellRendererComponent(tree: JTree,
                                                value: Object,
                                                sel: Boolean,
                                                expanded: Boolean,
                                                leaf: Boolean,
                                                row: Int,
                                                hasFocus: Boolean): Component =  {
        super.getTreeCellRendererComponent(
          tree, value, sel,
          expanded, leaf, row,
          hasFocus) 

        value match {
          case (nd: ProofNode) =>
            nd.status match {
              case Open => 
                setIcon(openIcon)
              case Irrelevant(_) => 
                setIcon(leafIcon)
              case Disproved => 
                setIcon(closedIcon)
              case Proved => 
                setIcon(closedIcon)
            }
          case _ =>
        }
        this 
      }
    }


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
