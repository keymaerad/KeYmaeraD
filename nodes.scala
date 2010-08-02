package DLBanyan



object Nodes {

  type NodeID = Int

  private var nextID = 0

  def nextNodeID : NodeID = {
    val res = nextID;
    nextID += 1;
    res
  }


  abstract class Status
  case object Proved extends Status
  case object Disproved extends Status
  case object Open extends Status
  case object Irrelevant extends Status


  abstract class ProofNode() {
    //val nodeType : NodeType = t
    val nodeID = nextNodeID 
    var children : List[NodeID] = Nil
    var status: Status  = Open

    def addchild(c: NodeID): Unit = {
      children = c :: children
    }
  }


  case class AndNode(rule: String, 
                     goal:Sequent,
                     svs: List[String]) extends ProofNode() {
    val schemavars = svs

   override def toString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("AndNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append("nodeID = " + nodeID + "\n")
      sb.append("status = " + status + "\n")
      sb.append("children = " + children + "\n")
      sb.append("schemavars = " + schemavars + "\n")
      sb.toString
   }

  }


  case class OrNode (rule: String, 
                goal: Sequent) extends ProofNode() {

   override def toString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("AndNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append("nodeID = " + nodeID + "\n")
      sb.append("status = " + status + "\n")
      sb.append("children = " + children + "\n")
      sb.toString
   }

  }

  case class BackendNode (rule: String, 
                          goal: Sequent) extends ProofNode() {
   status = Proved
    
   override def toString : String = {
      val sb = new StringBuilder()
      sb.append(Printing.stringOfSequent(goal) + "\n")
      sb.append("BackendNode\n")
      sb.append("rule = " + rule + "\n")
      sb.append("nodeID = " + nodeID + "\n")
      sb.toString
   }

  }



  val nodeTable = new scala.collection.mutable.HashMap[NodeID, ProofNode]


  def register(nd: ProofNode): Unit = {
    nodeTable.put(nd.nodeID, nd)
  }

  val nullNode = new OrNode("null", Sequent(Nil,Nil))
  register(nullNode)
  

}

