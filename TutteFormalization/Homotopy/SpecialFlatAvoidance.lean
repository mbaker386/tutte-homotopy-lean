import TutteFormalization.Homotopy.CorankThreeGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.22's first observation: a hyperplane with both decomposable opposite
intersections cannot contain an indecomposable corank-three flat below W∩Y. -/
theorem special_flat_not_below_hyperplane {F W Y I : Set α}
    (hF : Indecomposable M F) (hrF : natRank M F + 3 = natRank M M.E)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hI : IsHyperplane M I)
    (hL : CorankTwo M (W ∩ Y)) (hdL : ¬ Indecomposable M (W ∩ Y)) (hFL : F ⊆ W ∩ Y)
    (hdW : ¬ Indecomposable M (W ∩ I)) (hdY : ¬ Indecomposable M (Y ∩ I))
    (hcY : CorankTwo M (Y ∩ I)) : ¬ F ⊆ I := by
  intro hFI
  have hmeet := corankThree_unique_decomposable hF hrF hL hdL hFL hcY hdY
    (Set.subset_inter (hFL.trans Set.inter_subset_right) hFI)
  have hLI : W ∩ Y ⊆ I := hmeet.symm.subset.trans Set.inter_subset_right
  rcases (separation_hyperplanes hW hY hdL).2 I hI hLI with hi | hi
  · subst I
    exact hdW (by simpa using hyperplane_indecomposable hW)
  · subst I
    exact hdY (by simpa using hyperplane_indecomposable hY)
end TutteFormalization.Homotopy
