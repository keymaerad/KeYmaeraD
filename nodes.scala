package DLBanyan






object Nodes {

  type NodeID = Int

  private var nextID = 0

  def nextNodeID : NodeID = {
    val r = nextID;
    nextID += 1;
    r
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



  

}

