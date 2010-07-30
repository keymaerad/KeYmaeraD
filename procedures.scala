package DLBanyan

object Procedures {
  import Prover._

// for now, these things only close or disprove a goal.


  abstract class Procedure {
    def applies(sq: Sequent): Boolean

    def proceed(sq: Sequent, tm: Long): Option[Sequent]

    def proceed(sq: Sequent): Option[Sequent]

    def abort: Unit
  }


 


  object CohenHormanderProcedure extends Procedure {

    def applies(sq: Sequent) : Boolean = sq match {
      case Sequent(c,s) =>
        !(c.exists(x => ! firstclass(x)) ||  c.exists(x => ! firstclass(x)) )
    }


    def proceed(sq: Sequent): Option[Sequent] = sq match {
      case Sequent(c,s) => 
//       println("about to attempt quantifier elimination on:\n")
//       P.print_Formula(fm)
      val fm = Imp(AM.list_conj(c), AM.list_disj(s));
      val fm1 = AM.univ_close(fm);
       try{ 
 
        CV.start()
//         val r =  AM.real_elim_goal(fm)
         val r = AM.real_elim(fm1)
         if(r == True) {
           //println("success!")
           Some(Sequent(Nil,List(True)))
         } else {
           // TODO this doesn't actually mean disproved
           //println("failure!")
           //println("returned: " + P.string_of_Formula(r))
           Some(Sequent(Nil, List(r)))
         }      
       } catch {
         case e: CHAbort => 
           println("aborted quantifier elimination")
           None
       }
    }

// TODO
    def proceed(sq: Sequent, tm: Long): Option[Sequent] = {
      None
    }


    def abort : Unit = {
      CV.stop()
    }


  }


}
