package DLBanyan


abstract class Procedure {
  def applies(Sequent): Boolean
  def proceed(Sequent, Long): Option[Sequent]
  def proceed(Sequent): Sequent
}
