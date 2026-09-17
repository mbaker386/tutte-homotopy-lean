import TutteFormalization.Homotopy.NextJoinGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.1, decomposable L: corrected B.2, Diamond, off-hyperplane
choice and B.3 produce the actual on-G bridge and its triple carrier. -/
theorem exists_decomposable_bridge (hΓ : ModularCut M Γ) {G L H Z : Set α}
    (hG : Indecomposable M G) (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L)
    (hGL : G ⊆ L) (hH : IsHyperplane M H) (hZ : IsHyperplane M Z)
    (hHZ : H ≠ Z) (hLH : L ⊆ H) (hLZ : L ⊆ Z) (hoH : H ∉ Γ) :
    ∃ P T, Indecomposable M P ∧ natRank M P + 3 = natRank M M.E ∧
      G ⊆ P ∧ P ⊆ L ∧ IsHyperplane M T ∧ T ∉ Γ ∧ G ⊆ T ∧
      TutteAdjacent M T H ∧ TutteAdjacent M T Z ∧ Z ∩ T ∩ H = P := by
  obtain ⟨P,hP,hGP,hPL,hrP⟩ := exists_indecomposable_corankThree hG hL hnL hGL
  have hrH := hyperplane_natRank hH
  obtain ⟨V,W,hV,hW,hPV,hPW,hVH,hWH,hVW,hrV,hrW⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hH) hP (hPL.1.trans hLH) (by omega)
  have hVL : V ≠ L := fun he => hnL (he ▸ hV)
  have hVc : CorankTwo M V := (corankTwo_iff_natRank hV.1).mpr (by omega)
  obtain ⟨T,hT,hVT,hTH,hoT⟩ := exists_other_off_hyperplane hΓ hV hVc hH hVH hoH
  have hmeet := hyperplane_inter_eq_of_corankTwo hL hH hZ hHZ hLH hLZ
  have hTZ : T ≠ Z := by
    intro he
    have hsub : V ⊆ L := (Set.subset_inter hVH (hVT.trans_eq he)).trans_eq hmeet
    have hrL := corankTwo_natRank hL
    exact hVL (flat_eq_of_subset_of_natRank_le hV.1 hL.1 hsub (by omega))
  have hPT : P ⊆ T := hPV.trans hVT
  have hadj := third_hyperplane_adjacent hP hrP hL hnL hPL.1 hH hZ hHZ hLH hLZ
    hT hTH.symm hTZ.symm hPT
  have hnLT : ¬ L ⊆ T := by
    intro hLT
    have hdec : ¬ Indecomposable M (H ∩ Z) := hmeet.symm ▸ hnL
    rcases (separation_hyperplanes hH hZ hdec).2 T hT (hmeet.symm ▸ hLT) with he | he
    · exact hTH he
    · exact hTZ he
  have hrL := corankTwo_natRank hL
  have hi := (hyperplane_inter_of_cover hP.1 hL.1 hT hPL.1 hPT (by omega) hnLT).1
  refine ⟨P,T,hP,hrP,hGP,hPL.1,hT,hoT,hGP.trans hPT,hadj.1,hadj.2,?_⟩
  calc
    Z ∩ T ∩ H = (H ∩ Z) ∩ T := by ext x; simp only [Set.mem_inter_iff]; tauto
    _ = P := by rw [hmeet,hi]
end TutteFormalization.Homotopy
