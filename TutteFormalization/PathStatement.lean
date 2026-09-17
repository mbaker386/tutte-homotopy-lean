import TutteFormalization.Definitions

/-!
Independent specification for review against `thm:path-theorem`.
This proposition copies the complete statement, not a type inferred from its proof.
Only the approved definitions are imported. The explicit universe `u` corresponds
to the original declaration's single generalized universe parameter.
The setup snapshot is not evidence of reviewer approval or proof completion.
-/

namespace TutteFormalization

universe u

/-- Complete path-theorem proposition, independently stated for baseline review. -/
def PathTheoremStatement : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite]
    (hM : Connected M) (Γ : Set (Set α)) (hΓ : ModularCut M Γ)
    (F : Set α) (hF : Indecomposable M F) (hFproper : F ≠ M.E)
    (X Y : Set α) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ),
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ

end TutteFormalization
