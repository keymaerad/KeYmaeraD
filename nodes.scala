package DLBanyan






object Nodes {

  type NodeID = Int

  private var nextID = 0

  def nextNodeID : NodeID = {
    val res = nextID;
    nextID += 1;
    res
  }


  abstract class NodeType
  case object AndNode extends NodeType
  case object OrNode extends NodeType



  abstract class Status
  case object Proved extends Status
  case object Disproved extends Status
  case object Open extends Status
  case object Irrelevant extends Status


  case class ProofNode(t: NodeType, g: Goal) {
    //val nodeType : NodeType = t
    //val goal : Goal = g
    val nodeID = nextNodeID 
    var children : List[NodeID] = Nil
    var status = Open

  }


  val nodeTable = new scala.collection.mutable.HashMap[NodeID, ProofNode]


  def newNode(t: NodeType, g: Goal): ProofNode = {
    val res = ProofNode(t,g)
    nodeTable.put(res.nodeID, res)
    res
  }


  

}

