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
                svs: List[String]) extends ProofNode(rule,goal) {
    val schemavars = svs
    def print : Unit = {
      println("AndNode")
      println("rule = " + rule)
      println("nodeID = " + nodeID)
      println("status = " + status)
      println("children = " + children)
      println("schemavars = " + schemavars)

    }

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

  class OrNode (rule: String, 
                goal: Sequent) extends ProofNode(rule,goal) {
    def print : Unit = {
      println("OrNode")
      println("rule = " + rule)
      println("nodeID = " + nodeID)
      println("status = " + status)
      println("children = " + children)
    }

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





  val nodeTable = new scala.collection.mutable.HashMap[NodeID, ProofNode]


  def register(nd: ProofNode): Unit = {
    nodeTable.put(nd.nodeID, nd)
  }

  val nullNode = new OrNode("null", Sequent(Nil,Nil))
  register(nullNode)
  

}

