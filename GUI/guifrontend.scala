package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

import scala.swing._
import javax.swing.JPanel
import javax.swing.JTree
import javax.swing.JScrollPane
import javax.swing.JSplitPane
import javax.swing.JEditorPane
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import java.awt.event.ActionEvent
import java.awt.event.KeyEvent
import java.awt.Toolkit
import javax.swing.KeyStroke

import scala.actors.Actor
import scala.actors.Actor._

import DLBanyan.Nodes._
import DLBanyan.Tactics._
import DLBanyan._

import java.net.URL
import java.io.File
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
    try{
      val p = getPathAux(nd)
      p.reverse.toArray
    } catch {
      case e =>
        println(e)
        println("was starting at " + nd)
        throw new Error()
    }
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
  extends GridPanel(1,0) with TreeSelectionListener {

    import javax.swing.tree.DefaultTreeCellRenderer
    import java.awt.Component

    val frontactor = fa


    var  htmlPane :JEditorPane = null 
    var tree : JTree = null


  val tm = new TreeModel(this)
  fa ! ('registergui, tm)

  tree = new JTree(tm)
  tree.setCellRenderer(new MyRenderer)
  tree.getSelectionModel().setSelectionMode(
    TreeSelectionModel.SINGLE_TREE_SELECTION)

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

  //@TODO Add the split pane to this panel.
  //contents = splitPane
  peer.add(splitPane)


    /** Required by TreeSelectionListener interface. */
    def valueChanged(e: TreeSelectionEvent) : Unit = {
          tree.getLastSelectedPathComponent() match {
            case (nd : ProofNode) => 
              htmlPane.setText(nd.toPrettyString)
              TreeActions.gotonode(nd)
            case _ => null
          }

    }


    def fireNodesInserted(path: Array[Object]): Unit = {
      val tpath = new javax.swing.tree.TreePath(path)
      tree.expandPath(tpath)
    }



    class MyRenderer extends DefaultTreeCellRenderer {

      import javax.swing.Icon

      def loadicon(filename: String, default: Icon): Icon = {

        val i = try {
          new javax.swing.ImageIcon(filename)
        }catch {
          case e => 
            println ("using default icon")
            default
          }
        i
      }

      setOpenIcon(loadicon("icons/open.png", openIcon))
      val provedIcon = loadicon("icons/proved.png", closedIcon)
      val irrelevantIcon = loadicon("icons/irrelevant.png", leafIcon)
      val disprovedIcon = loadicon("icons/disproved.png", closedIcon)


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
                setIcon(irrelevantIcon)
              case Disproved => 
                setIcon(disprovedIcon)
              case Proved => 
                setIcon(provedIcon)
            }
          case _ =>
        }
        this 
      }
    }


}



object FE {

  var recentFiles : List[String] = Nil;

  def createAndShowGUI(fa: Actor) : Unit =  {

    //Create and set up the window.
    val frame = new MainFrame {
	  title="Yandle";
	  val keymask = toolkit.getMenuShortcutKeyMask();
      //Add content to the window.
	  contents = new FrontEnd(fa)
          val recent = new Menu("Open Recent")
          menuBar = new MenuBar {
	      contents += new Menu("File") {
		  val open = new MenuItem(Action("Open") {
		  val chooser = new FileChooser(new File("."))
		    if (chooser.showOpenDialog(menuBar) == 
                      FileChooser.Result.Approve) {
                        val pth = chooser.selectedFile.getCanonicalPath
                        recentFiles = pth :: recentFiles
                        recent.contents += new MenuItem(Action(pth){
 		          fa ! ('load, pth)
                        })
 		        fa ! ('load, pth)
 		    };
		  })
	    open.action.accelerator = Some(KeyStroke.getKeyStroke(KeyEvent.VK_O, keymask));
	    contents += open

		contents += new Separator
                contents += recent

		contents += new Separator
		val quit = new MenuItem(Action("Quit") {
		  visible = false
		  close
		  fa ! ('quit)
		})
	    quit.action.accelerator = Some(KeyStroke.getKeyStroke(KeyEvent.VK_O, ActionEvent.CTRL_MASK));
    	contents += quit
    }
	    contents += new Menu("Prove") {
	      val teasy = new MenuItem(Action("All Easy") 
                                       {fa ! ('tactic, alleasyT)})
		  teasy.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_E, keymask));
		  contents += teasy
	      contents += new MenuItem(Action("Hide Then Close") 
                                       {fa ! ('tactic, hidethencloseT)})
	      }
  	    }
      //frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)

      pack()
      visible =true
    }
  }


  def start(fa: Actor) : Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      def run() {
        createAndShowGUI(fa)
      }
    });    
  }

  


}
