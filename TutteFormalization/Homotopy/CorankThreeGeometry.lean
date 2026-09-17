import TutteFormalization.Homotopy.CorankThree

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {P L I X Y Z : Set α}

/-- The rank calculation used twice in B.3: two distinct corank-two flats
above a corank-three flat have a hyperplane join. -/
theorem corankTwo_join_isHyperplane (hP : M.IsFlat P)
    (hrP : natRank M P + 3 = natRank M M.E) (hL : CorankTwo M L) (hI : CorankTwo M I)
    (hPL : P ⊆ L) (hPI : P ⊆ I) (hne : L ≠ I) : IsHyperplane M (M.closure (L ∪ I)) := by
  have hrL := corankTwo_natRank hL
  have hrI := corankTwo_natRank hI
  have hLJ : L ⊆ M.closure (L ∪ I) :=
    M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hIJ : I ⊆ M.closure (L ∪ I) :=
    M.subset_closure_of_subset' Set.subset_union_right hI.1.subset_ground
  have hneq : L ≠ M.closure (L ∪ I) := by
    intro h
    have hIL : I ⊆ L := hIJ.trans_eq h.symm
    exact hne (flat_eq_of_subset_of_natRank_le hI.1 hL.1 hIL (by omega)).symm
  have hlo := natRank_lt_of_flat_ssubset hL.1 (M.isFlat_closure _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hLJ,hneq⟩)
  have hbound := natRank_submodular M L I
  have hmeet := natRank_mono (M := M) (Set.subset_inter hPL hPI)
  exact isHyperplane_of_natRank (M.isFlat_closure _) (by omega)

/-- B.3's first incidence claim, prior to applying Diamond. -/
theorem corankThree_two_intersections (hP : M.IsFlat P)
    (hrP : natRank M P + 3 = natRank M M.E) (hL : CorankTwo M L)
    (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hLX : L ⊆ X) (hLY : L ⊆ Y) (hZ : IsHyperplane M Z) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hI : CorankTwo M I) (hPI : P ⊆ I) (hIZ : I ⊆ Z) : I = Z ∩ X ∨ I = Z ∩ Y := by
  have hmeet := hyperplane_inter_eq_of_corankTwo hL hX hY hXY hLX hLY
  have two : ∀ H, IsHyperplane M H → L ⊆ H → H = X ∨ H = Y := by
    intro H hH hLH
    exact (separation_hyperplanes hX hY (by simpa only [hmeet] using hnL)).2 H hH
      (by simpa only [hmeet] using hLH)
  have hn : L ≠ I := by
    intro h
    rcases two Z hZ (h ▸ hIZ) with h | h
    · exact hXZ h.symm
    · exact hYZ h.symm
  have hJ := corankTwo_join_isHyperplane hP hrP hL hI hPL hPI hn
  have hLJ : L ⊆ M.closure (L ∪ I) :=
    M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hIJ : I ⊆ M.closure (L ∪ I) :=
    M.subset_closure_of_subset' Set.subset_union_right hI.1.subset_ground
  rcases two _ hJ hLJ with hj | hj
  · exact Or.inl (hyperplane_inter_eq_of_corankTwo hI hZ hX hXZ.symm hIZ
      (hIJ.trans_eq hj)).symm
  · exact Or.inr (hyperplane_inter_eq_of_corankTwo hI hZ hY hYZ.symm hIZ
      (hIJ.trans_eq hj)).symm

/-- Diamond supplies both of B.3's possible intermediate flats as indecomposable. -/
theorem corankThree_intersections_indecomposable (hP : Indecomposable M P)
    (hrP : natRank M P + 3 = natRank M M.E) (hL : CorankTwo M L)
    (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hLX : L ⊆ X) (hLY : L ⊆ Y) (hZ : IsHyperplane M Z) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hPZ : P ⊆ Z) : Indecomposable M (Z ∩ X) ∧ Indecomposable M (Z ∩ Y) := by
  have hrZ := hyperplane_natRank hZ
  obtain ⟨V,W,hV,hW,hPV,hPW,hVZ,hWZ,hVW,hVr,hWr⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hZ) hP hPZ (by omega)
  have hVc : CorankTwo M V := (corankTwo_iff_natRank hV.1).mpr (by omega)
  have hWc : CorankTwo M W := (corankTwo_iff_natRank hW.1).mpr (by omega)
  have hcV := corankThree_two_intersections hP.1 hrP hL hnL hPL hX hY hXY hLX hLY
    hZ hXZ hYZ hVc hPV hVZ
  have hcW := corankThree_two_intersections hP.1 hrP hL hnL hPL hX hY hXY hLX hLY
    hZ hXZ hYZ hWc hPW hWZ
  rcases hcV with hv | hv <;> rcases hcW with hw | hw
  · exact False.elim (hVW (hv.trans hw.symm))
  · exact ⟨hv ▸ hV,hw ▸ hW⟩
  · exact ⟨hw ▸ hW,hv ▸ hV⟩
  · exact False.elim (hVW (hv.trans hw.symm))

/-- B.3's final consequence: the given decomposable corank-two flat is unique. -/
theorem corankThree_unique_decomposable (hP : Indecomposable M P)
    (hrP : natRank M P + 3 = natRank M M.E) (hL : CorankTwo M L)
    (hnL : ¬ Indecomposable M L) (hPL : P ⊆ L)
    (hI : CorankTwo M I) (hnI : ¬ Indecomposable M I) (hPI : P ⊆ I) : I = L := by
  by_contra hIL
  obtain ⟨X,Y,hX,hY,hXY,hLX,hLY⟩ := corankTwo_hyperplane_pair hL
  obtain ⟨U,V,hU,hV,hUV,hIU,hIV⟩ := corankTwo_hyperplane_pair hI
  have hmeet := hyperplane_inter_eq_of_corankTwo hL hX hY hXY hLX hLY
  have hmeetI := hyperplane_inter_eq_of_corankTwo hI hU hV hUV hIU hIV
  have other : ∃ Z, IsHyperplane M Z ∧ I ⊆ Z ∧ X ≠ Z ∧ Y ≠ Z := by
    by_contra hn
    have hUeq : U = X ∨ U = Y := by
      by_cases hUX : U = X
      · exact Or.inl hUX
      · right; by_contra hUY; exact hn ⟨U,hU,hIU,Ne.symm hUX,Ne.symm hUY⟩
    have hVeq : V = X ∨ V = Y := by
      by_cases hVX : V = X
      · exact Or.inl hVX
      · right; by_contra hVY; exact hn ⟨V,hV,hIV,Ne.symm hVX,Ne.symm hVY⟩
    rcases hUeq with rfl | rfl <;> rcases hVeq with rfl | rfl
    · exact hUV rfl
    · exact hIL (hmeetI.symm.trans hmeet)
    · exact hIL (hmeetI.symm.trans (by simpa only [Set.inter_comm] using hmeet))
    · exact hUV rfl
  obtain ⟨Z,hZ,hIZ,hXZ,hYZ⟩ := other
  have hconn := corankThree_intersections_indecomposable hP hrP hL hnL hPL
    hX hY hXY hLX hLY hZ hXZ hYZ (hPI.trans hIZ)
  rcases corankThree_two_intersections hP.1 hrP hL hnL hPL hX hY hXY hLX hLY
    hZ hXZ hYZ hI hPI hIZ with heq | heq
  · exact hnI (heq ▸ hconn.1)
  · exact hnI (heq ▸ hconn.2)
end TutteFormalization.Homotopy
