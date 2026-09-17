import TutteFormalization

/-! Axiom audit and boundary checks for the statement-review stage. -/

open TutteFormalization

namespace StatementChecks

theorem connected_of_subsingleton_ground {α : Type*} (M : Matroid α)
    (hE : M.E.Subsingleton) : Connected M := by
  rintro ⟨A, B, ⟨a, ha⟩, ⟨b, hb⟩, hd, hu, _⟩
  have haE : a ∈ M.E := hu ▸ Set.mem_union_left B ha
  have hbE : b ∈ M.E := hu ▸ Set.mem_union_right A hb
  have hab : a = b := hE haE hbE
  exact Set.disjoint_left.1 hd ha (hab ▸ hb)

theorem empty_modularCut {α : Type*} (M : Matroid α) : ModularCut M ∅ where
  isFlat := by simp
  upward := by simp
  inter_mem := by simp

def constantPath {α : Type*} {M : Matroid α} (H : Set α)
    (hH : IsHyperplane M H) : TuttePath M where
  length := 0
  vertex := fun _ => H
  isHyperplane := fun _ => hH
  adjacent := fun i => Fin.elim0 i

theorem constantPath_spec {α : Type*} {M : Matroid α} (H F : Set α)
    (Γ : Set (Set α)) (hH : IsHyperplane M H) (hF : F ⊆ H) (hΓ : H ∉ Γ) :
    (constantPath H hH).origin = H ∧ (constantPath H hH).terminus = H ∧
      (constantPath H hH).On F ∧ (constantPath H hH).Off Γ :=
  ⟨rfl, rfl, fun _ => hF, fun _ => hΓ⟩

end StatementChecks

#check TutteFormalization.path_theorem
#print axioms TutteFormalization.Connected
#print axioms TutteFormalization.IsHyperplane
#print axioms TutteFormalization.Indecomposable
#print axioms TutteFormalization.ModularPair
#print axioms TutteFormalization.ModularCut
#print axioms TutteFormalization.CorankTwo
#print axioms TutteFormalization.TutteAdjacent
#print axioms TutteFormalization.TuttePath
#print axioms TutteFormalization.TuttePath.origin
#print axioms TutteFormalization.TuttePath.terminus
#print axioms TutteFormalization.TuttePath.On
#print axioms TutteFormalization.TuttePath.Off
#print axioms TutteFormalization.TuttePath.carrier
#print axioms StatementChecks.connected_of_subsingleton_ground
#print axioms StatementChecks.empty_modularCut
#print axioms StatementChecks.constantPath
#print axioms StatementChecks.constantPath_spec
#print axioms TutteFormalization.path_theorem
