import TutteFormalization.Homotopy.CorankThreeReduction

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.3 chooses T above L, different from the preceding off hyperplane,
preferentially in the cut. Every other hyperplane in that pencil is off. -/
theorem exists_preferred_hyperplane (hΓ : ModularCut M Γ) {L H : Set α}
    (hL : CorankTwo M L) (hH : IsHyperplane M H) (hLH : L ⊆ H) (hoH : H ∉ Γ) :
    ∃ T, IsHyperplane M T ∧ L ⊆ T ∧ T ≠ H ∧
      ∀ Q, IsHyperplane M Q → L ⊆ Q → Q ≠ T → Q ∉ Γ := by
  classical
  by_cases hex : ∃ T, IsHyperplane M T ∧ L ⊆ T ∧ T ∈ Γ
  · obtain ⟨T,hT,hLT,ht⟩ := hex
    refine ⟨T,hT,hLT,(fun he => hoH (he ▸ ht)),?_⟩
    intro Q hQ hLQ hQT hq
    exact hQT (cut_hyperplanes_unique_above hΓ hL hH hLH hoH hQ hT hLQ hLT hq ht)
  · obtain ⟨X,Y,hX,hY,hXY,hLX,hLY⟩ := corankTwo_hyperplane_pair hL
    have hall : ∀ Q, IsHyperplane M Q → L ⊆ Q → Q ∉ Γ := fun Q hQ hLQ hq => hex ⟨Q,hQ,hLQ,hq⟩
    by_cases he : X = H
    · exact ⟨Y,hY,hLY,(fun hy => hXY (he.trans hy.symm)),fun Q hQ hLQ _ => hall Q hQ hLQ⟩
    · exact ⟨X,hX,hLX,he,fun Q hQ hLQ _ => hall Q hQ hLQ⟩
end TutteFormalization.Homotopy
