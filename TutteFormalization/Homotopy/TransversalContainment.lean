import TutteFormalization.Homotopy.TransversalRanks

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.21's containment calculation: joining a one-rank extension to Y∩I
produces a hyperplane, hence is Y or I; escaping Y selects I. -/
theorem extension_below_other_hyperplane {A B Y I : Set α}
    (hY : IsHyperplane M Y) (hI : IsHyperplane M I) (hYI : Y ≠ I)
    (hc : CorankTwo M (Y ∩ I)) (hd : ¬ Indecomposable M (Y ∩ I))
    (hB : M.IsFlat B) (hAB : A ⊆ B) (hAL : A ⊆ Y ∩ I)
    (hrB : natRank M B = natRank M A + 1) (hnBY : ¬ B ⊆ Y) : B ⊆ I := by
  let J := M.closure (B ∪ (Y ∩ I))
  have hLJ : Y ∩ I ⊆ J := M.subset_closure_of_subset' Set.subset_union_right hc.1.subset_ground
  have hBJ : B ⊆ J := M.subset_closure_of_subset' Set.subset_union_left hB.subset_ground
  have hn : Y ∩ I ≠ J := fun heq => hnBY (hBJ.trans (heq.symm.subset.trans Set.inter_subset_left))
  have hlt := natRank_lt_of_flat_ssubset hc.1 (M.isFlat_closure _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hLJ,hn⟩)
  have hs := natRank_submodular M B (Y ∩ I)
  have hi := natRank_mono (M := M) (Set.subset_inter hAB hAL)
  have hLr := corankTwo_natRank hc
  have hJ : IsHyperplane M J := by
    apply isHyperplane_of_natRank (M.isFlat_closure _)
    dsimp only [J] at *
    omega
  rcases (separation_hyperplanes hY hI hd).2 J hJ hLJ with h | h
  · exact False.elim (hnBY (hBJ.trans_eq h))
  · exact hBJ.trans_eq h
end TutteFormalization.Homotopy
