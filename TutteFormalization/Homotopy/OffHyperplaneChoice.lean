import TutteFormalization.Homotopy.RankTwo

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.17's choice: above an indecomposable corank-two flat below an off-cut
hyperplane, another containing hyperplane avoids the cut. -/
theorem exists_other_off_hyperplane (hΓ : ModularCut M Γ) {L W : Set α}
    (hL : Indecomposable M L) (hcL : CorankTwo M L)
    (hW : IsHyperplane M W) (hLW : L ⊆ W) (hWo : W ∉ Γ) :
    ∃ H, IsHyperplane M H ∧ L ⊆ H ∧ H ≠ W ∧ H ∉ Γ := by
  by_contra hn
  have allcut : ∀ H, IsHyperplane M H → L ⊆ H → H ≠ W → H ∈ Γ := by
    intro H hH hLH hHW
    by_contra hHo
    exact hn ⟨H,hH,hLH,hHW,hHo⟩
  have forbid : ∀ H K, IsHyperplane M H → IsHyperplane M K → L ⊆ H → L ⊆ K →
      H ≠ K → H ≠ W → K ≠ W → False := by
    intro H K hH hK hLH hLK hHK hHW hKW
    have hi := hyperplane_inter_eq_of_corankTwo hcL hH hK hHK hLH hLK
    have hmod := hyperplanes_modularPair_of_corankTwo hH hK hHK (by simpa only [hi] using hcL)
    have hmem : L ∈ Γ := hi ▸ hΓ.inter_mem H K (allcut H hH hLH hHW) (allcut K hK hLK hKW) hmod
    exact hWo (hΓ.upward L W hmem hW.1 hLW)
  obtain ⟨H,K,Q,hH,hK,hQ,hHK,hHQ,hKQ,hLH,hLK,hLQ⟩ :=
    (corankTwo_indecomposable_iff_three hcL).mp hL
  by_cases hHW : H = W
  · subst H
    exact forbid K Q hK hQ hLK hLQ hKQ hHK.symm hHQ.symm
  by_cases hKW : K = W
  · subst K
    exact forbid H Q hH hQ hLH hLQ hHQ hHK hKQ.symm
  exact forbid H K hH hK hLH hLK hHK hHW hKW
end TutteFormalization.Homotopy
