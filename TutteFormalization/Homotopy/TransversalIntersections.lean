import TutteFormalization.Homotopy.TransversalRanks

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- A flat covering D is obtained by adjoining one point. If D lies in both
sides of a flat cover of E, the cover lies entirely in one side. -/
theorem flat_cover_under_one_side {D G W Y : Set α}
    (hD : M.IsFlat D) (hG : M.IsFlat G) (hDG : D ⊆ G)
    (hrG : natRank M G = natRank M D + 1)
    (hW : M.IsFlat W) (hY : M.IsFlat Y) (hDW : D ⊆ W) (hDY : D ⊆ Y)
    (hunion : W ∪ Y = M.E) : G ⊆ W ∨ G ⊆ Y := by
  have hnGD : ¬ G ⊆ D := by
    intro h
    have hr := natRank_mono (M := M) h
    omega
  obtain ⟨a,haG,haD⟩ := Set.not_subset.mp hnGD
  have hcsub : M.closure (insert a D) ⊆ G :=
    (M.closure_mono (Set.insert_subset haG hDG)).trans_eq hG.closure
  have hcr := natRank_closure_insert hD (hG.subset_ground haG) haD
  have heq := flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) hG hcsub (by omega)
  have ham : a ∈ W ∪ Y := hunion.symm ▸ hG.subset_ground haG
  rcases ham with haW | haY
  · exact Or.inl (heq ▸ (M.closure_mono (Set.insert_subset haW hDW)).trans_eq hW.closure)
  · exact Or.inr (heq ▸ (M.closure_mono (Set.insert_subset haY hDY)).trans_eq hY.closure)

/-- B.15's Diamond argument: a two-rank indecomposable transversal has two
opposite indecomposable intersections, each covering the carrier D. -/
theorem transversal_intersections {D B W Y : Set α}
    (hD : Indecomposable M D) (hB : Indecomposable M B) (hDB : D ⊆ B)
    (hrB : natRank M B = natRank M D + 2)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y)
    (hDW : D ⊆ W) (hDY : D ⊆ Y) (hunion : W ∪ Y = M.E)
    (hnBW : ¬ B ⊆ W) (hnBY : ¬ B ⊆ Y) :
    Indecomposable M (B ∩ W) ∧ Indecomposable M (B ∩ Y) ∧
      natRank M (B ∩ W) = natRank M D + 1 ∧
      natRank M (B ∩ Y) = natRank M D + 1 ∧
      (B ∩ W) ∩ (B ∩ Y) = D ∧ M.closure ((B ∩ W) ∪ (B ∩ Y)) = B := by
  obtain ⟨U,V,hU,hV,hDU,hDV,hUB,hVB,hUV,hUr,hVr⟩ :=
    exists_indecomposable_diamond hB hD hDB hrB
  have hj := cover_flats_join_eq hB.1 hU.1 hV.1 hUB hVB hUr hVr hrB hUV
  have hi := cover_flats_inter_eq hD.1 hU.1 hV.1 hDU hDV hUr hVr hUV
  have cover_inter : ∀ G H, M.IsFlat G → M.IsFlat H → G ⊆ B → G ⊆ H →
      natRank M G = natRank M D + 1 → ¬ B ⊆ H → G = B ∩ H := by
    intro G H hG hH hGB hGH hrG hnBH
    have hn : B ∩ H ≠ B := fun heq => hnBH (heq.symm.subset.trans Set.inter_subset_right)
    have hlt := natRank_lt_of_flat_ssubset (flat_inter hB.1 hH) hB.1
      (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,hn⟩)
    exact flat_eq_of_subset_of_natRank_le hG (flat_inter hB.1 hH)
      (Set.subset_inter hGB hGH) (by omega)
  have together : ∀ H, M.IsFlat H → U ⊆ H → V ⊆ H → B ⊆ H := by
    intro H hH hUH hVH
    rw [← hj]
    exact (M.closure_mono (Set.union_subset hUH hVH)).trans_eq hH.closure
  rcases flat_cover_under_one_side hD.1 hU.1 hDU hUr hW.1 hY.1 hDW hDY hunion with hUW | hUY <;>
    rcases flat_cover_under_one_side hD.1 hV.1 hDV hVr hW.1 hY.1 hDW hDY hunion with hVW | hVY
  · exact False.elim (hnBW (together W hW.1 hUW hVW))
  · have hu := cover_inter U W hU.1 hW.1 hUB hUW hUr hnBW
    have hv := cover_inter V Y hV.1 hY.1 hVB hVY hVr hnBY
    rw [← hu,← hv]
    exact ⟨hU,hV,hUr,hVr,hi,hj⟩
  · have hu := cover_inter U Y hU.1 hY.1 hUB hUY hUr hnBY
    have hv := cover_inter V W hV.1 hW.1 hVB hVW hVr hnBW
    rw [← hu,← hv]
    exact ⟨hV,hU,hVr,hUr,by simpa only [Set.inter_comm] using hi,
      by simpa only [Set.union_comm] using hj⟩
  · exact False.elim (hnBY (together Y hY.1 hUY hVY))
end TutteFormalization.Homotopy
