package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

import scala.swing.Frame

class FrontEnd extends Frame {
  
  def test : Unit = {
    println("hello world")
  }


  def main(args: Array[String]): Unit = {
    val w = new FrontEnd();
//    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    w.size = new java.awt.Dimension(400, 320)
    w.centerOnScreen
    w.visible = true
  }


}
