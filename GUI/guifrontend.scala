package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

import scala.swing._
import javax.swing._

class FrontEnd extends JFrame("SWEET")  {
  
  def test : Unit = {
    println("hello world")
  }

/*
  override def closeOperation() : Unit = {
    System.exit(0)
  }
*/

}

object FE {

  def main : Unit = {
    val w = new FrontEnd 
           
    w.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    w.setSize(420, 300)
//    w.centerOnScreen
    w.setVisible(true)
    println(w)

  }

}
