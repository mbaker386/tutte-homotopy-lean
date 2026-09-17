import TutteFormalization.Homotopy.CutHyperplaneCriterion
import TutteFormalization.IndecomposableComplement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.22's maximal-rank argument with the eligible containing hyperplane tied
to G. This is the authorized HD-007 repair; an unrelated I is never fixed. -/
theorem maximal_eligible_join_hyperplane (hΓ : ModularCut M Γ) {F G T I : Set α}
    (hF : Indecomposable M F) (hG : Indecomposable M G) (hT : M.IsFlat T)
    (hGF : G ⊆ F) (hI : IsHyperplane M I) (hGI : G ⊆ I) (hTI : T ⊆ I) (hIo : I ∉ Γ)
    (hFT : M.closure (F ∪ T) = M.E)
    (maximal : ∀ G', Indecomposable M G' → G ⊆ G' → G' ⊆ F →
      (∃ H, IsHyperplane M H ∧ G' ⊆ H ∧ T ⊆ H ∧ H ∉ Γ) → natRank M G' ≤ natRank M G) :
    IsHyperplane M (M.closure (G ∪ T)) := by
  let J := M.closure (G ∪ T)
  have hJ : M.IsFlat J := M.isFlat_closure _
  have hJI : J ⊆ I := (M.closure_mono (Set.union_subset hGI hTI)).trans_eq hI.1.closure
  have hGJ : G ⊆ J := M.subset_closure_of_subset' Set.subset_union_left hG.1.subset_ground
  have hTJ : T ⊆ J := M.subset_closure_of_subset' Set.subset_union_right hT.subset_ground
  have hNchoice : ∃ N, IsHyperplane M N ∧ J ⊆ N ∧
      (N ∈ Γ ∨ ∀ H, IsHyperplane M H → J ⊆ H → H ∉ Γ) := by
    by_cases hh : ∃ N, IsHyperplane M N ∧ J ⊆ N ∧ N ∈ Γ
    · obtain ⟨N,hN,hJN,hmem⟩ := hh
      exact ⟨N,hN,hJN,Or.inl hmem⟩
    · exact ⟨I,hI,hJI,Or.inr (fun H hH hJH hmem => hh ⟨H,hH,hJH,hmem⟩)⟩
  obtain ⟨N,hN,hJN,hchoice⟩ := hNchoice
  have hnFN : ¬ F ⊆ N := by
    intro hFN
    have hEN : M.E ⊆ N := hFT ▸
      (M.closure_mono (Set.union_subset hFN (hTJ.trans hJN))).trans_eq hN.1.closure
    exact hN.2.1 (Set.Subset.antisymm hN.1.subset_ground hEN)
  obtain ⟨G',hG',hGG',hG'F,hnG'N,hrG'⟩ := exists_indecomposable_cover_not_subset
    hF hG hN.1 hGF (hGJ.trans hJN) hnFN
  let K := M.closure (G' ∪ T)
  have hK : M.IsFlat K := M.isFlat_closure _
  have hJK : J ⊆ K := M.closure_mono (Set.union_subset_union_left T hGG')
  have hG'K : G' ⊆ K := M.subset_closure_of_subset' Set.subset_union_left hG'.1.subset_ground
  have hTK : T ⊆ K := M.subset_closure_of_subset' Set.subset_union_right hT.subset_ground
  have hnKN : ¬ K ⊆ N := fun h => hnG'N (hG'K.trans h)
  have hnJK : J ≠ K := fun heq => hnKN (heq.symm.subset.trans hJN)
  have hlo := natRank_lt_of_flat_ssubset hJ hK (Set.ssubset_iff_subset_ne.mpr ⟨hJK,hnJK⟩)
  have hjk : M.closure (G' ∪ J) = K := by
    dsimp only [J,K]
    rw [M.closure_union_closure_right_eq]
    congr 1
    ext x
    constructor
    · rintro (hx | hx | hx)
      · exact Or.inl hx
      · exact Or.inl (hGG' hx)
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
  have hu := natRank_submodular M G' J
  rw [hjk] at hu
  have hm := natRank_mono (M := M) (Set.subset_inter hGG' hGJ)
  have hrK : natRank M K = natRank M J + 1 := by omega
  have hKE : K = M.E := by
    by_contra hnKE
    have allcut : ∀ H, IsHyperplane M H → K ⊆ H → H ∈ Γ := by
      intro H hH hKH
      by_contra hHo
      have hh := maximal G' hG' hGG' hG'F ⟨H,hH,hG'K.trans hKH,hTK.trans hKH,hHo⟩
      omega
    have hKΓ := proper_cut_mem_of_all_hyperplanes hΓ hK hnKE allcut
    rcases hchoice with hNΓ | hoff
    · obtain ⟨hmeet,hmod⟩ := hyperplane_inter_of_cover hJ hK hN hJK hJN hrK hnKN
      have hJΓ : J ∈ Γ := hmeet ▸ hΓ.inter_mem K N hKΓ hNΓ hmod
      exact hIo (hΓ.upward J I hJΓ hI.1 hJI)
    · obtain ⟨e,heE,heK⟩ := Set.not_subset.mp (show ¬ M.E ⊆ K from fun h =>
        hnKE (Set.Subset.antisymm hK.subset_ground h))
      obtain ⟨H,hH,hKH,_⟩ := exists_hyperplane_superset_notMem hK heE heK
      exact hoff H hH (hJK.trans hKH) (allcut H hH hKH)
  apply isHyperplane_of_natRank hJ
  rw [hKE] at hrK
  omega
end TutteFormalization.Homotopy
