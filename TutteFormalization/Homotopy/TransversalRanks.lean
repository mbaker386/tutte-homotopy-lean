import TutteFormalization.Homotopy.CorankThreeGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.11: the join of a one-rank transversal and the special corank-three
flat is indecomposable of corank two. The rank argument only needs flatness
of the transversal; indecomposability follows from B.3 at the special flat. -/
theorem transversal_cover_join {D A P L : Set α}
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hA : M.IsFlat A) (hDA : D ⊆ A) (hDP : D ⊆ P)
    (hrA : natRank M A = natRank M D + 1) (hnAL : ¬ A ⊆ L) :
    Indecomposable M (M.closure (A ∪ P)) ∧ CorankTwo M (M.closure (A ∪ P)) := by
  let J := M.closure (A ∪ P)
  have hJ : M.IsFlat J := M.isFlat_closure _
  have hPJ : P ⊆ J := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have hAJ : A ⊆ J := M.subset_closure_of_subset' Set.subset_union_left hA.subset_ground
  have hnPJ : P ≠ J := fun heq => hnAL (hAJ.trans (heq.symm.subset.trans hPL))
  have hlo := natRank_lt_of_flat_ssubset hP.1 hJ (Set.ssubset_iff_subset_ne.mpr ⟨hPJ,hnPJ⟩)
  have hsub := natRank_submodular M A P
  have hmeet := natRank_mono (M := M) (Set.subset_inter hDA hDP)
  have hrJ : natRank M J + 2 = natRank M M.E := by change _ + natRank M J ≤ _ at hsub; omega
  have hcJ : CorankTwo M J := (corankTwo_iff_natRank hJ).mpr hrJ
  refine ⟨?_,hcJ⟩
  by_contra hdec
  have heq := corankThree_unique_decomposable hP hrP hL hnL hPL hcJ hdec hPJ
  exact hnAL (hAJ.trans_eq heq)

/-- B.13: a two-rank transversal escaping both opposite hyperplanes has a
hyperplane join with the special corank-three flat. -/
theorem transversal_two_join_hyperplane {D B P L W Y : Set α}
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hWY : W ≠ Y)
    (hLW : L ⊆ W) (hLY : L ⊆ Y)
    (hB : M.IsFlat B) (hDB : D ⊆ B) (hDP : D ⊆ P)
    (hrB : natRank M B = natRank M D + 2) (hnBW : ¬ B ⊆ W) (hnBY : ¬ B ⊆ Y) :
    IsHyperplane M (M.closure (B ∪ P)) := by
  let J := M.closure (B ∪ P)
  have hJ : M.IsFlat J := M.isFlat_closure _
  have hPJ : P ⊆ J := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have hBJ : B ⊆ J := M.subset_closure_of_subset' Set.subset_union_left hB.subset_ground
  have hnPJ : P ≠ J := fun heq => hnBW (hBJ.trans (heq.symm.subset.trans (hPL.trans hLW)))
  have hlo := natRank_lt_of_flat_ssubset hP.1 hJ (Set.ssubset_iff_subset_ne.mpr ⟨hPJ,hnPJ⟩)
  have hsub := natRank_submodular M B P
  have hmeet := natRank_mono (M := M) (Set.subset_inter hDB hDP)
  change _ + natRank M J ≤ _ at hsub
  have hbound : natRank M J + 1 ≤ natRank M M.E := by omega
  apply isHyperplane_of_natRank hJ
  by_contra hne
  have hcJ : CorankTwo M J := (corankTwo_iff_natRank hJ).mpr (by omega)
  obtain ⟨H,K,hH,hK,hHK,hJH,hJK⟩ := corankTwo_hyperplane_pair hcJ
  have hWH : W ≠ H := fun h => hnBW (hBJ.trans (hJH.trans_eq h.symm))
  have hYH : Y ≠ H := fun h => hnBY (hBJ.trans (hJH.trans_eq h.symm))
  rcases corankThree_two_intersections hP.1 hrP hL hnL hPL hW hY hWY hLW hLY
    hH hWH hYH hcJ hPJ hJH with heq | heq
  · exact hnBW (hBJ.trans (heq.subset.trans Set.inter_subset_right))
  · exact hnBY (hBJ.trans (heq.subset.trans Set.inter_subset_right))
end TutteFormalization.Homotopy
