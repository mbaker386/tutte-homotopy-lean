import TutteFormalization.Homotopy.OffJoinDecomposable
import TutteFormalization.Homotopy.OffJoinIndecomposable

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Complete local Case 2.2.1: construct L from the actual carrier cover,
then use the indecomposable or decomposable branch with all premises supplied. -/
theorem off_join_shortcut (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) {D F G H K J : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hiF : Indecomposable M F) (hF : F = H ∩ K ∩ J)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hD : M.IsFlat D) (hiG : Indecomposable M G)
    (hDG : D ⊆ G) (hDF : D ⊆ F) (hrG : natRank M G = natRank M D + 1)
    (hGH : G ⊆ H) (hGK : ¬ G ⊆ K) (hrD : natRank M M.E - natRank M D ≤ n+1)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ)
    (hoZ : M.closure (M.closure (G ∪ F) ∪ (K ∩ J)) ∉ Γ) :
    ∃ q : TuttePath M,
      Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) q ∧
      q.On D ∧ outsideCount q G <
        outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) G := by
  have hFH : F ⊆ H := by rw [hF]; exact fun _ hx => hx.1.1
  have hFK : F ⊆ K := by rw [hF]; exact fun _ hx => hx.1.2
  have hFJ : F ⊆ J := by rw [hF]; exact Set.inter_subset_right
  obtain ⟨hL,hLH,_⟩ := corankThree_first_join hΓ hD hiG.1 hiF.1 hDG hDF hrG hrF
    hH hGH hFH hFK hGK hoH
  have hGL : G ⊆ M.closure (G ∪ F) := M.subset_closure_of_subset' Set.subset_union_left hiG.1.subset_ground
  have hFL : F ⊆ M.closure (G ∪ F) := M.subset_closure_of_subset' Set.subset_union_right hiF.1.subset_ground
  by_cases hiL : Indecomposable M (M.closure (G ∪ F))
  · exact off_join_indec_shortcut hΓ hH hK hJ hHK hKJ hF hrF hL hiL hFL hLH
      hGL hGK hDG (hDF.trans hFJ) hoH hoK hoJ hoZ
  · exact off_join_decomp_shortcut hM hΓ hlower hH hK hJ hHK hKJ hiF hF hrF hL hiL hFL hLH
      hiG hGL hGK hDG hDF hrD hoH hoK hoJ hoZ
end TutteFormalization.Homotopy
