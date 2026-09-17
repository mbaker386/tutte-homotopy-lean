import TutteFormalization.Homotopy.ResidualLast

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Common rank and cut calculation for the residual joins W1,W2,W3 and
U°. An extra flat escaping a cut hyperplane gives another off hyperplane
in a pencil already containing an off hyperplane. -/
theorem extra_join_off (hΓ : ModularCut M Γ) {F B I C H : Set α}
    (hF : M.IsFlat F) (hrF : natRank M F + 3 = natRank M M.E)
    (hB : CorankTwo M B) (hI : CorankTwo M I) (hFB : F ⊆ B) (hFI : F ⊆ I)
    (hC : IsHyperplane M C) (hBC : B ⊆ C) (hCΓ : C ∈ Γ) (hnIC : ¬ I ⊆ C)
    (hH : IsHyperplane M H) (hBH : B ⊆ H) (hoH : H ∉ Γ) :
    IsHyperplane M (M.closure (B ∪ I)) ∧ M.closure (B ∪ I) ≠ C ∧ M.closure (B ∪ I) ∉ Γ := by
  have hBI : B ≠ I := fun he => hnIC (he ▸ hBC)
  have hJ := corankTwo_join_isHyperplane hF hrF hB hI hFB hFI hBI
  have hBJ : B ⊆ M.closure (B ∪ I) := M.subset_closure_of_subset' Set.subset_union_left hB.1.subset_ground
  have hIJ : I ⊆ M.closure (B ∪ I) := M.subset_closure_of_subset' Set.subset_union_right hI.1.subset_ground
  have hne : M.closure (B ∪ I) ≠ C := fun he => hnIC (hIJ.trans_eq he)
  refine ⟨hJ,hne,?_⟩
  intro hm
  exact hne (cut_hyperplanes_unique_above hΓ hB hH hBH hoH hJ hC hBJ hBC hm hCΓ)
end TutteFormalization.Homotopy
