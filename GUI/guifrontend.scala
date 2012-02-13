package KeYmaeraD.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

import scala.swing._
import javax.swing.JPanel
import javax.swing.JTree
import javax.swing.JScrollPane
import javax.swing.JSplitPane
import javax.swing.JEditorPane
import javax.swing.JPopupMenu
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeSelectionModel;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import java.awt.event.ActionEvent
import java.awt.event.KeyEvent
import java.awt.Toolkit
import java.awt.Font
import javax.swing.KeyStroke

import scala.actors.Actor
import scala.actors.Actor._

import KeYmaeraD.Nodes._
import KeYmaeraD.Tactics._
import KeYmaeraD._

import scala.collection.JavaConversions._
import java.awt.datatransfer.DataFlavor
import java.awt.datatransfer.Transferable
import java.awt.datatransfer.UnsupportedFlavorException
import java.awt.dnd.DropTarget
import java.awt.dnd.DropTargetAdapter
import java.awt.dnd.DropTargetDropEvent
import java.awt.dnd.DropTargetListener

import java.net.URL
import java.io.File
import java.io.IOException
import java.io._
import java.awt.Dimension
import java.awt.GridLayout


class TreeModel(fe: FrontEnd) extends javax.swing.tree.TreeModel {
  import javax.swing.event.TreeModelEvent
  import javax.swing.event.TreeModelListener

  import KeYmaeraD.Nodes._

  val frontend = fe

  val treeModelListeners =  
    new scala.collection.mutable.HashSet[TreeModelListener]()

  def addTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.add(l)
  }

  def removeTreeModelListener(l: TreeModelListener): Unit =  {
        treeModelListeners.remove(l)
  }

  def fireProved(nd: ProofNode) : Unit = {
    val path = getPath(nd)
    frontend.fireProved(path)
  }

  def fireNodesInserted(pt: ProofNode, newnds: List[ProofNode]): Unit = {
    val path = getPath(pt)
    val c: Array[Object] = newnds.toArray
    val newlength = pt.getChildren.length 
    val oldlength = newlength - newnds.length
    val ci: Array[Int] = Range(oldlength, newlength).toArray
    val e = new TreeModelEvent(this, path, ci, c)
    for (l <- treeModelListeners) {
      l.treeNodesInserted(e)
//      l.treeStructureChanged(e)
    }
    frontend.fireNodesInserted(path)
  }

  def fireChanged(nd: ProofNode): Unit = {
    val path = getPath(nd)
    val e = new TreeModelEvent(this, path)
    for (l <- treeModelListeners) {
      l.treeNodesChanged(e)
      }
  }

  def fireNewRoot(nd: ProofNode): Unit = {
    val path:Array[Object] = List(nd).toArray
    val e = new TreeModelEvent(this, path)
    for (l <- treeModelListeners) {
      l.treeStructureChanged(e)
    }
  }

  def getPathAux(nd: ProofNode): List[Object] = nd.getParent match {
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
    try {
      val p = getPathAux(nd)
      p.reverse.toArray
    } catch {
      case e =>
        println(e)
        println("was starting at " + nd)
        throw new Error()
    }
  }

  def getIndexOfChild(parent: Any, child: Any): Int = (parent, child) match {
    case (p: ProofNode, c: ProofNode) =>
      p.getChildren.indexOf(c.nodeID)
    case _ => 
      throw new Error("child not found")
  }

  def getChild(parent: Any, index: Int): Object = parent match {
    case (pn: ProofNode) =>
      val r = getnode(pn.getChildren.apply(index))
//      println("getting child  " + index + " of " + pn)
//      println("it is " + r)
      r
    case _ => 
      null
  }

  def getChildCount(parent: Any): Int = parent match {
    case (pn: ProofNode) =>
      pn.getChildren.length
    case _ => 
      0
  }
  
  def getRoot(): Object = {
    rootNode
  }

  def isLeaf(node: Any): Boolean = node match {
    case (pn: ProofNode) =>
      pn.getChildren.isEmpty
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

    var htmlPane :JEditorPane = null 
    var tree : JTree = null

    val tm = new TreeModel(this)
    fa ! ('registergui, tm)

    tree = new JTree(tm)
    tree.setCellRenderer(new MyRenderer)
    tree.getSelectionModel().setSelectionMode(
      TreeSelectionModel.SINGLE_TREE_SELECTION)

    //Listen for when the selection changes.
    tree.addTreeSelectionListener(this)
    // Popup Menu per node
    tree.addMouseListener(new MouseAdapter() {
      var node : ProofNode = null
      val popup : PopupMenu = new PopupMenu
      popup.peer.setInvoker(tree)
      popup.add(new MenuItem(Action("Stop")
                             {println("aborting job " + node.nodeID)
	                      fa ! ('abort, node.nodeID)}))

      override def mousePressed(e : MouseEvent) {
	if (e.isPopupTrigger()) {
	  val loc = e.getPoint();
          tree.getPathForLocation(loc.x, loc.y).getLastPathComponent() match {
            case (nd : ProofNode) =>
              node = nd
              popup.show(tree, loc.x, loc.y)
            case _ => null
          }
	}
      }
    })

    //Create the scroll pane and add the tree to it. 
    val treeView = new JScrollPane(tree)
  
    //Create the HTML viewing pane.
    htmlPane = new JEditorPane()
    htmlPane.setEditable(false)
    tm.getRoot() match {
       case (nd : ProofNode) =>
         htmlPane.setText(nd.toPrettyString)
       case _ => null
      }
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

    def fireProved(path: Array[Object]): Unit = {
      val tpath = new javax.swing.tree.TreePath(path)
      tree.collapsePath(tpath)
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
        } catch {
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
      val abortedIcon = loadicon("icons/aborted.png", closedIcon)



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
            nd.getStatus match {
              case Open => 
                setIcon(openIcon)
              case Irrelevant(_) => 
                setIcon(irrelevantIcon)
              case Disproved => 
                setIcon(disprovedIcon)
              case Proved => 
                setIcon(provedIcon)
              case Aborted => 
                setIcon(abortedIcon)
            }
          case _ =>
            throw new Error("not a proof node")
        }
        this
      }
    }
}


class PopupMenu extends Component
{
  override lazy val peer : JPopupMenu = new JPopupMenu

  def add(item:MenuItem) : Unit = { peer.add(item.peer) }
  def setVisible(visible:Boolean) : Unit = { peer.setVisible(visible) }
  /* Create any other peer methods here */
  def show(c:java.awt.Component, x:Int, y:Int) : Unit = {peer.show(c,x,y)}
}

object FE {
  val propertiesFiles = System.getProperty("user.home") + File.separator + ".keymaerad";

  var recentFiles : List[String] = Nil;

  var recent : Menu = null;

  var mf: Frame = null;

  var fe : FrontEnd = null;
  

  def createAndShowGUI(fa: Actor) : Unit =  {
    //Create and set up the window.
    mf = new Frame {
      title="KeYmaeraD";
      val keymask = toolkit.getMenuShortcutKeyMask();
      //Add content to the window.
      fe = new FrontEnd(fa)
      contents = fe
      recent = new Menu("Open Recent")
	  // read properties
      try {
        val props = new ObjectInputStream(new FileInputStream(propertiesFiles))
        recentFiles = props.readObject().asInstanceOf[List[String]]
        props.close()
        recentFiles.foreach(pth => recent.contents += new MenuItem(Action(pth){
              fa ! ('load, pth)
          }))
      } catch {
	    case e:FileNotFoundException => Nil
	    case e:IOException => e.printStackTrace();
      }

      menuBar = new MenuBar {
	contents += new Menu("File") {
	  val open = new MenuItem(Action("Open") {
	    val chooser = new FileChooser(new File("."))
	    if (chooser.showOpenDialog(menuBar) == 
              FileChooser.Result.Approve) {
              val pth = chooser.selectedFile
              loadProblem(fa, pth)
 	    };
	  })
	  open.action.accelerator = Some(KeyStroke.getKeyStroke(KeyEvent.VK_O, keymask));
	  contents += open
          
          val reopen = new MenuItem(Action("Reopen") {
            fa ! 'reload
          })
          reopen.action.accelerator =
            Some(KeyStroke.getKeyStroke(KeyEvent.VK_R, keymask));
          contents += reopen

	  contents += new Separator
          contents += recent

	  contents += new Separator
	  val quit = new MenuItem(Action("Quit") {
	    visible = false
	    close
	  })
	  quit.action.accelerator = Some(KeyStroke.getKeyStroke(KeyEvent.VK_Q, ActionEvent.CTRL_MASK));
    	    contents += quit
        }
	contents += new Menu("View") {
		contents += new MenuItem(Action("Font Size Smaller") {fe.htmlPane.setFont( fe.htmlPane.getFont().deriveFont(fe.htmlPane.getFont().getSize()*0.8f))})
		contents += new MenuItem(Action("Font Size Larger") {fe.htmlPane.setFont( fe.htmlPane.getFont().deriveFont(fe.htmlPane.getFont().getSize()*1.25f))})
	}
	contents += new Menu("Prove") {

          val trunscript = new MenuItem(Action("Scripted Tactic")
                                        {fa ! ('runscripttactic)})
          trunscript.peer.setAccelerator(  
            KeyStroke.getKeyStroke(KeyEvent.VK_U, keymask));
          contents += trunscript

	  val tstop = new MenuItem(Action("Stop")
                                   {fa ! ('abortall)})
	  tstop.action.accelerator = Some(KeyStroke.getKeyStroke(
            KeyEvent.VK_Z, 
            ActionEvent.CTRL_MASK));
	  contents += tstop
		 
	  val tdefault = new MenuItem(Action("Default") 
                                   {fa ! ('tactic, easiestT)})
	  tdefault.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_D, keymask));
	  contents += tdefault

	  val teasy = new MenuItem(Action("All Easy") 
                                   {fa ! ('tactic, alleasyT)})
	  teasy.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_E, keymask));
	  contents += teasy
          val thtc = new MenuItem(Action("Hide Then Close") 
                                  {fa ! ('tactic, hidethencloseT)})
	  thtc.peer.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, keymask));
	  contents +=  thtc

	}

    }
      
      override def close = {
	fa ! ('quit)
        super.close
      }

      override def closeOperation = close

      pack()
      visible = true
      }
    
      var fileOpener = new DropTargetAdapter() {
        def drop(event: DropTargetDropEvent) = {
          try {
            val transferable = event.getTransferable()
            if (transferable.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) {
              try {
                event.acceptDrop(event.getSourceActions());
                val files = transferable.getTransferData(DataFlavor.javaFileListFlavor)
                files match {
	              case l:java.util.List[File] => l.foreach(
                    file => file match {
                      case f:File => loadProblem(fa, f)
                      case _ => event.dropComplete(false)
                    })
	                event.dropComplete(true);
	              case l:List[File] => l.foreach(
                    file => file match {
                      case f:File => loadProblem(fa, f)
                      case _ => event.dropComplete(false)
                    })
	                event.dropComplete(true);
                  case _ => println("Don't understand drag and drop type" + files.getClass);
                    event.dropComplete(false)
                }
              }
            } else {
              event.rejectDrop()
            }
          } catch {
	        case e:IOException => event.rejectDrop()
            case e:UnsupportedFlavorException => event.rejectDrop()
          }
        }
      }
      val fileDropTarget = new DropTarget(mf.peer, fileOpener);
      mf.peer.setDropTarget(fileDropTarget);
      fe.htmlPane.setDropTarget(fileDropTarget);


  }
  
  def loadProblem(fa: Actor, path: File) : Unit = {
	val pth = path.getCanonicalPath
    if (!recentFiles.contains(pth)) {
	    recentFiles = pth :: recentFiles
      recent.contents += new MenuItem(Action(pth){
          fa ! ('load, pth)
      })
      // write properties
      try {
        val props = new ObjectOutputStream(new FileOutputStream(propertiesFiles))
        props.writeObject(recentFiles)
        props.close()
      } catch {
	    case e:IOException => e.printStackTrace();
	  }	
	}
	fa ! ('load, pth)
  }

  def start(fa: Actor) : Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      def run() {
        createAndShowGUI(fa)
      }
    });    
  }

  


}
