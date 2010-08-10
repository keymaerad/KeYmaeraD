package DLBanyan.GUI

import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent

import scala.swing.Frame


class FrontEnd extends Frame {
  
  def test : Unit = {
    println("hello world")
  }

  override def closeOperation() : Unit = {
    System.exit(0)
  }


}

object FE {

  def main : Unit = {
    val w = new FrontEnd();
    w.size = new java.awt.Dimension(400, 320)
    w.centerOnScreen
    w.visible = true
  }

}
