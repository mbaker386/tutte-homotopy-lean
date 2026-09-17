import TutteFormalization.Homotopy.TransversalIntersections

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The corank certificates accompanying B.3's indecomposable intersections. -/
theorem third_hyperplane_adjacent {P L W Y H : Set α}
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hWY : W ≠ Y)
    (hLW : L ⊆ W) (hLY : L ⊆ Y) (hH : IsHyperplane M H)
    (hWH : W ≠ H) (hYH : Y ≠ H) (hPH : P ⊆ H) :
    TutteAdjacent M H W ∧ TutteAdjacent M H Y := by
  have hrH := hyperplane_natRank hH
  obtain ⟨U,V,hU,hV,hPU,hPV,hUH,hVH,hUV,hUr,hVr⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hH) hP hPH (by omega)
  have hUc : CorankTwo M U := (corankTwo_iff_natRank hU.1).mpr (by omega)
  have hVc : CorankTwo M V := (corankTwo_iff_natRank hV.1).mpr (by omega)
  have hu := corankThree_two_intersections hP.1 hrP hL hnL hPL hW hY hWY hLW hLY
    hH hWH hYH hUc hPU hUH
  have hv := corankThree_two_intersections hP.1 hrP hL hnL hPL hW hY hWY hLW hLY
    hH hWH hYH hVc hPV hVH
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (hUV (hu.trans hv.symm))
  · exact ⟨⟨hWH.symm,hu ▸ hU,hu ▸ hUc⟩,⟨hYH.symm,hv ▸ hV,hv ▸ hVc⟩⟩
  · exact ⟨⟨hWH.symm,hv ▸ hV,hv ▸ hVc⟩,⟨hYH.symm,hu ▸ hU,hu ▸ hUc⟩⟩
  · exact False.elim (hUV (hu.trans hv.symm))
end TutteFormalization.Homotopy
