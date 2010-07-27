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


  abstract class ProofNode(r: String, g: Sequent) {
    //val nodeType : NodeType = t
    val rule = r
    val goal = g
    val nodeID = nextNodeID 
    var children : List[NodeID] = Nil
    var status = Open
    def print: Unit
  }

  class AndNode(rule: String, 
                goal:Sequent,
                fvs: List[String]) extends ProofNode(rule,goal) {
    val freevars = fvs
    def print : Unit = {
      println("AndNode")
      println("rule = " + rule)
      println("nodeID = " + nodeID)
      println("status = " + status)
      println("children = " + children)
      println("freevars = " + freevars)

    }
  }

  class OrNode (rule: String, 
                goal: Sequent) extends ProofNode(rule,goal) {
    def print : Unit = {
      println("OrNode")
      println("rule = " + rule)
      println("nodeID = " + nodeID)
      println("status = " + status)
      println("children = " + children)
    }

  }





  val nodeTable = new scala.collection.mutable.HashMap[NodeID, ProofNode]


  def register(nd: ProofNode): Unit = {
    nodeTable.put(nd.nodeID, nd)
  }

  val nullNode = new OrNode("null", Sequent(Nil,Nil))
  register(nullNode)
  

}

