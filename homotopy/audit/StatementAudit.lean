import TutteFormalization.Homotopy.Statement
import TutteFormalization.Homotopy.Theorem

universe u
example : TutteFormalization.HomotopyTheoremStatement.{u} :=
  @TutteFormalization.homotopy_theorem.{u}

set_option pp.universes true in
#print TutteFormalization.HomotopyTheoremStatement
set_option pp.all true in
#check @TutteFormalization.homotopy_theorem
#print axioms TutteFormalization.HomotopyTheoremStatement
#print axioms TutteFormalization.homotopy_theorem
