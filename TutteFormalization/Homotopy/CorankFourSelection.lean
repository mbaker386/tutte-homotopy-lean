import TutteFormalization.Homotopy.MaximalEligibleJoin

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.22/HD-007: maximize among flats together with an eligible containing
hyperplane. The returned hyperplane is G∨T itself and contains the selected G. -/
theorem exists_corankFour_eligible (hΓ : ModularCut M Γ) {D F T : Set α}
    (hD : Indecomposable M D) (hF : Indecomposable M F) (hT : M.IsFlat T)
    (hDF : D ⊆ F) (hDT : D ⊆ T)
    (hrF : natRank M F + 3 = natRank M M.E) (hrT : natRank M T = natRank M D + 3)
    (hex : ∃ I, IsHyperplane M I ∧ T ⊆ I ∧ I ∉ Γ)
    (hno : ∀ I, IsHyperplane M I → T ⊆ I → I ∉ Γ → ¬ F ⊆ I)
    (hFT : M.closure (F ∪ T) = M.E) :
    ∃ G, Indecomposable M G ∧ D ⊆ G ∧ G ⊂ F ∧
      natRank M G + 4 = natRank M M.E ∧
      IsHyperplane M (M.closure (G ∪ T)) ∧ M.closure (G ∪ T) ∉ Γ := by
  let C : Set (Set α) := {G | Indecomposable M G ∧ D ⊆ G ∧ G ⊆ F ∧
    ∃ I, IsHyperplane M I ∧ G ⊆ I ∧ T ⊆ I ∧ I ∉ Γ}
  have hfin : C.Finite := M.ground_finite.powerset.subset (fun _ hg => hg.1.1.subset_ground)
  obtain ⟨I₀,hI₀,hTI₀,hI₀o⟩ := hex
  have hnonempty : C.Nonempty := ⟨D,hD,Set.Subset.rfl,hDF,I₀,hI₀,hDT.trans hTI₀,hTI₀,hI₀o⟩
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image C (natRank M) hfin hnonempty
  obtain ⟨I,hI,hGI,hTI,hIo⟩ := hG.2.2.2
  have hstrict : G ⊂ F := Set.ssubset_iff_subset_ne.mpr ⟨hG.2.2.1,fun heq =>
    hno I hI hTI hIo (heq ▸ hGI)⟩
  have hJ := maximal_eligible_join_hyperplane hΓ hF hG.1 hT hG.2.2.1 hI hGI hTI hIo hFT
    (fun G' hG' hGG' hG'F helig => hmax G' ⟨hG',hG.2.1.trans hGG',hG'F,helig⟩)
  have hJI : M.closure (G ∪ T) ⊆ I := (M.closure_mono (Set.union_subset hGI hTI)).trans_eq hI.1.closure
  have hJo : M.closure (G ∪ T) ∉ Γ := fun hmem => hIo
    (hΓ.upward _ I hmem hI.1 hJI)
  have hlo := natRank_lt_of_flat_ssubset hG.1.1 hF.1 hstrict
  have hjr := hyperplane_natRank hJ
  have hu := natRank_submodular M G T
  have hm := natRank_mono (M := M) (Set.subset_inter hG.2.1 hDT)
  exact ⟨G,hG.1,hG.2.1,hstrict,by omega,hJ,hJo⟩

/-- Both joins with T used in B.22 and B.23 span because they contain two
 distinct pole hyperplanes. This is also the explicit HD-008 justification. -/
theorem join_spans_of_distinct_poles {B C F T : Set α}
    (hBT : B ⊆ T) (hCT : C ⊆ T)
    (hB : IsHyperplane M (M.closure (B ∪ F)))
    (hC : IsHyperplane M (M.closure (C ∪ F)))
    (hne : M.closure (B ∪ F) ≠ M.closure (C ∪ F)) : M.closure (F ∪ T) = M.E := by
  have hBJ : M.closure (B ∪ F) ⊆ M.closure (F ∪ T) :=
    M.closure_mono (Set.union_subset (hBT.trans Set.subset_union_right) Set.subset_union_left)
  have hCJ : M.closure (C ∪ F) ⊆ M.closure (F ∪ T) :=
    M.closure_mono (Set.union_subset (hCT.trans Set.subset_union_right) Set.subset_union_left)
  have hj := hyperplane_join_eq_ground hB hC hne
  apply Set.Subset.antisymm (M.closure_subset_ground _)
  rw [← hj]
  exact M.closure_subset_closure_of_subset_closure (Set.union_subset hBJ hCJ)
end TutteFormalization.Homotopy
