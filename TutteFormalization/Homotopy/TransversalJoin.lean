import TutteFormalization.Homotopy.OppositePoles
import TutteFormalization.Homotopy.CutHyperplaneCriterion

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.18's two rank bounds, with the already-proved intersection. -/
theorem rank_join_of_distinct_covers {A B C : Set α}
    (hB : M.IsFlat B) (hC : M.IsFlat C)
    (hrB : natRank M B = natRank M A + 1) (hrC : natRank M C = natRank M A + 1)
    (hne : B ≠ C) (hi : B ∩ C = A) :
    natRank M (M.closure (B ∪ C)) = natRank M A + 2 := by
  have hbJ : B ⊆ M.closure (B ∪ C) := M.subset_closure_of_subset' Set.subset_union_left hB.subset_ground
  have hcJ : C ⊆ M.closure (B ∪ C) := M.subset_closure_of_subset' Set.subset_union_right hC.subset_ground
  have hneq : B ≠ M.closure (B ∪ C) := by
    intro heq
    exact hne (flat_eq_of_subset_of_natRank_le hC hB (hcJ.trans_eq heq.symm) (by omega)).symm
  have hlo := natRank_lt_of_flat_ssubset hB (M.isFlat_closure _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hbJ,hneq⟩)
  have hu := natRank_submodular M B C
  rw [hi] at hu
  omega

namespace SpecialData

/-- B.19: there is an off-cut hyperplane containing T=B∨C. -/
theorem exists_off_above_join (s : SpecialData M Γ) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 3 ≤ n) (hrD : natRank M s.D + (n+1) = natRank M M.E)
    {A B C : Set α} (ha : s.TypeA A) (hb : s.TypeB B) (hc : s.TypeB C)
    (hBC : B ≠ C) (hinter : B ∩ C = A)
    (hB₁off : M.closure (B ∪ s.F₁) ∉ Γ)
    (hC₁mem : M.closure (C ∪ s.F₁) ∈ Γ)
    (hC₂off : M.closure (C ∪ s.F₂) ∉ Γ) :
    ∃ I, IsHyperplane M I ∧ M.closure (B ∪ C) ⊆ I ∧ I ∉ Γ := by
  let T := M.closure (B ∪ C)
  have hT : M.IsFlat T := M.isFlat_closure _
  have hBT : B ⊆ T := M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hCT : C ⊆ T := M.subset_closure_of_subset' Set.subset_union_right hc.1.1.subset_ground
  have hrA := ha.2.2.1
  have hrB := hb.2.2.1
  have hrC := hc.2.2.1
  have hrT : natRank M T = natRank M A + 2 :=
    rank_join_of_distinct_covers hb.1.1 hc.1.1 (by omega) (by omega) hBC hinter
  have hproper : T ≠ M.E := by intro heq; have := congrArg (natRank M) heq; omega
  by_contra hno
  have hall : ∀ I, IsHyperplane M I → T ⊆ I → I ∈ Γ := by
    intro I hI hTI
    by_contra hIo
    exact hno ⟨I,hI,hTI,hIo⟩
  have hTΓ := proper_cut_mem_of_all_hyperplanes hΓ hT hproper hall
  have hU := s.typeB_first_pole hc
  have hCU : C ⊆ M.closure (C ∪ s.F₁) :=
    M.subset_closure_of_subset' Set.subset_union_left hc.1.1.subset_ground
  have hnTU : ¬ T ⊆ M.closure (C ∪ s.F₁) := by
    intro hTU
    have hF₁U : s.F₁ ⊆ M.closure (C ∪ s.F₁) :=
      M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground
    have heq := pole_eq_of_containment (hBT.trans hTU) hF₁U hU (s.typeB_first_pole hb)
    exact hB₁off (heq ▸ hC₁mem)
  obtain ⟨hmeet,hmod⟩ := hyperplane_inter_of_cover hc.1.1 hT hU hCT hCU (by omega) hnTU
  have hCΓ : C ∈ Γ := hmeet ▸ hΓ.inter_mem T _ hTΓ hC₁mem hmod
  exact hC₂off (hΓ.upward C _ hCΓ (s.typeB_second_pole hc).1
    (M.subset_closure_of_subset' Set.subset_union_left hc.1.1.subset_ground))
end SpecialData
end TutteFormalization.Homotopy
