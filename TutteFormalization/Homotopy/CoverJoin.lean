import TutteFormalization.Homotopy.FinalCoverSelection

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The modular rank bound used when the final-induction cover G is joined
with a local flat F. The intersection equality is derived, not assumed. -/
theorem cover_join_rank {D G F : Set α} (hD : M.IsFlat D) (hG : M.IsFlat G)
    (hF : M.IsFlat F) (hDG : D ⊆ G) (hDF : D ⊆ F)
    (hrG : natRank M G = natRank M D + 1) (hne : ¬ G ⊆ F) :
    G ∩ F = D ∧ natRank M (M.closure (G ∪ F)) = natRank M F + 1 := by
  have hproper : G ∩ F ⊂ G := Set.ssubset_iff_subset_ne.mpr
    ⟨Set.inter_subset_left,fun he => hne (he ▸ Set.inter_subset_right)⟩
  have hlt := natRank_lt_of_flat_ssubset (flat_inter hG hF) hG hproper
  have hi : G ∩ F = D := (flat_eq_of_subset_of_natRank_le hD (flat_inter hG hF)
    (Set.subset_inter hDG hDF) (by omega)).symm
  have hGJ : G ⊆ M.closure (G ∪ F) := M.subset_closure_of_subset' Set.subset_union_left hG.subset_ground
  have hFJ : F ⊆ M.closure (G ∪ F) := M.subset_closure_of_subset' Set.subset_union_right hF.subset_ground
  have hs : F ⊂ M.closure (G ∪ F) := Set.ssubset_iff_subset_ne.mpr
    ⟨hFJ,fun he => hne (hGJ.trans_eq he.symm)⟩
  have hlo := natRank_lt_of_flat_ssubset hF (M.isFlat_closure _) hs
  have hhi := natRank_submodular M G F
  rw [hi] at hhi
  exact ⟨hi,by omega⟩
end TutteFormalization.Homotopy
