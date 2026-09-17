import TutteFormalization.PathStatement
import TutteFormalization.PathTheorem

/-!
Compare the actual theorem to the independently stated proposition.
Success with the main proof placeholder is expected and is not proof completion.
The complete elaborated type below is part of the human review record.
-/

universe u

example : TutteFormalization.PathTheoremStatement.{u} :=
  @TutteFormalization.path_theorem.{u}

set_option pp.universes true in
#print TutteFormalization.PathTheoremStatement

set_option pp.all true in
#check @TutteFormalization.path_theorem

#print axioms TutteFormalization.PathTheoremStatement
#print axioms TutteFormalization.path_theorem
