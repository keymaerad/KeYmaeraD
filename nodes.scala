package DLBanyan



object Nodes {

  type NodeID = Int

  private var nextID = 0

  def nextNodeID : NodeID = {
    val res = nextID;
    nextID += 1;
    res
  }


  sealed abstract class Status
  case object Proved extends Status
  case object Disproved extends Status
  case object Open extends Status
  case class Irrelevant(old: Status) extends Status


  abstract class ProofNode() {
    //val nodeType : NodeType = t
    val nodeID = nextNodeID 
    var children : List[NodeID] = Nil
    var parent : Option[NodeID] = None

    var status: Status  = Open

    def addchild(c: NodeID): Unit = synchronized{
      children =  children ++ List(c)
    }

    def getchildren : List[NodeID] = synchronized{
      children
    }

    override def toString: String = {
      "ProofNode " + nodeID.toString
    }

    def toPrettyString: String = {
      val sb = new StringBuilder()
      sb.append("nodeID = " + nodeID + "\n")
      sb.append("status = " + status + "\n")
      sb.append("parent = " + parent + "\n")
      sb.append("children = " + children + "\n")
      sb.toString
    }

  }


  case class AndNode(rule: String, 
                     goal:Sequent,
                     svs: List[String]) extends ProofNode() {
    val schemavars = svs

    override def toString: String = {
      nodeID.toString + " & " + rule 
    }

   override def toPrettyString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("AndNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append("schemavars = " + schemavars + "\n")
      sb.append(super.toPrettyString)
      sb.toString
   }

  }


  case class OrNode (rule: String, 
                goal: Sequent) extends ProofNode() {

    override def toString: String = {
      nodeID.toString + " | " + rule
    }

   override def toPrettyString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("OrNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append(super.toPrettyString)
      sb.toString
   }

    override def hashCode : Int = {
      nodeID.hashCode
    }

  }

  case class WorkingNode (rule: String, 
                          goal: Sequent) extends ProofNode() {
   status = Open
    
    override def toString: String = {
      "WorkingNode " + nodeID.toString
    }

   override def toPrettyString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("WorkingNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append(super.toPrettyString)
      sb.toString
   }

  }




  case class DoneNode (rule: String, 
                       goal: Sequent) extends ProofNode() {
   status = Proved
    
    override def toString: String = {
      "DoneNode " + nodeID.toString
    }

   override def toPrettyString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("DoneNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append(super.toPrettyString)
      sb.toString
   }

  }


  // do I need the synchronization?
  class SyncHashMap extends
    scala.collection.mutable.HashMap[NodeID, ProofNode] with
    scala.collection.mutable.SynchronizedMap[NodeID, ProofNode]

  
  val nodeTable = 
    new SyncHashMap
  
  def register(nd: ProofNode): Unit = {
    nodeTable.put(nd.nodeID, nd)
  }

  val nullNode = new OrNode("null", Sequent(Nil,Nil))
  register(nullNode)
  
  var rootNode = nullNode

  def getnode(ndID: NodeID) : ProofNode = nodeTable.get(ndID) match {
    case Some(nd) =>
      nd
    case None =>
      throw new Error("node does not exist: " + ndID) 
    
  }

}

