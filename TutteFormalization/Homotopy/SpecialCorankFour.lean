import TutteFormalization.Homotopy.SecondIntersection
import TutteFormalization.Homotopy.TransversalJoin
import TutteFormalization.Homotopy.CorankFourSelection
import TutteFormalization.Homotopy.SpecialFlatAvoidance

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.22 for the actual opposite-pole configuration, also recording HD-008's
spanning join for F₂ that is needed by the following Complement application. -/
theorem exists_corankFour_choice (s : SpecialData M Γ)
    (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ} (hn : 3 ≤ n)
    (hlower : Lower M Γ n) (hrD : natRank M s.D + (n+1) = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) {A B C : Set α}
    (ha : s.TypeA A) (hb : s.TypeB B) (hc : s.TypeB C)
    (hAW : A ⊆ s.W) (hAB : A ⊆ B) (hAC : A ⊆ C)
    (hBC : B ≠ C) (hinter : B ∩ C = A)
    (hoB : M.closure (B ∪ s.F₁) ∉ Γ) (hiB : M.closure (B ∪ s.F₂) ∈ Γ)
    (hiC : M.closure (C ∪ s.F₁) ∈ Γ) (hoC : M.closure (C ∪ s.F₂) ∉ Γ) :
    ∃ G I, Indecomposable M G ∧ s.D ⊆ G ∧ G ⊂ s.F₁ ∧
      natRank M G + 4 = natRank M M.E ∧
      I = M.closure (G ∪ M.closure (B ∪ C)) ∧ IsHyperplane M I ∧ I ∉ Γ ∧
      (¬ Indecomposable M (s.W ∩ I) ∧ CorankTwo M (s.W ∩ I)) ∧
      (¬ Indecomposable M (s.Y ∩ I) ∧ CorankTwo M (s.Y ∩ I)) ∧
      M.closure (s.F₁ ∪ I) = M.E ∧ M.closure (s.F₂ ∪ I) = M.E := by
  let T := M.closure (B ∪ C)
  have hT : M.IsFlat T := M.isFlat_closure _
  have hBT : B ⊆ T := M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hCT : C ⊆ T := M.subset_closure_of_subset' Set.subset_union_right hc.1.1.subset_ground
  have hrA := ha.2.2.1
  have hrB := hb.2.2.1
  have hrC := hc.2.2.1
  have hrT' := rank_join_of_distinct_covers hb.1.1 hc.1.1 (by omega) (by omega) hBC hinter
  have hrT : natRank M T = natRank M s.D + 3 := by dsimp only [T]; omega
  have hF₁T : M.closure (s.F₁ ∪ T) = M.E :=
    join_spans_of_distinct_poles hBT hCT (s.typeB_first_pole hb) (s.typeB_first_pole hc)
      (fun heq => hoB (heq ▸ hiC))
  have hF₂T : M.closure (s.F₂ ∪ T) = M.E :=
    join_spans_of_distinct_poles hBT hCT (s.typeB_second_pole hb) (s.typeB_second_pole hc)
      (fun heq => hoC (heq ▸ hiB))
  have hex := s.exists_off_above_join hΓ hn hrD ha hb hc hBC hinter hoB hiC hoC
  have obs : ∀ I, IsHyperplane M I → T ⊆ I → I ∉ Γ →
      (¬ Indecomposable M (s.W ∩ I) ∧ CorankTwo M (s.W ∩ I)) ∧
      (¬ Indecomposable M (s.Y ∩ I) ∧ CorankTwo M (s.Y ∩ I)) := by
    intro I hI hTI hIo
    exact ⟨s.second_intersection_decomposable hM hΓ hn hlower hrD hnot ha hb hc hAW hAB hAC
      hoB hoC hI (hBT.trans hTI) (hCT.trans hTI) hIo,
      s.first_intersection_decomposable hM hΓ hn hlower hrD hnot ha hb hc hAW hAB hAC
      hoB hoC hI (hBT.trans hTI) (hCT.trans hTI) hIo⟩
  have hno : ∀ I, IsHyperplane M I → T ⊆ I → I ∉ Γ → ¬ s.F₁ ⊆ I := by
    intro I hI hTI hIo
    have hh := obs I hI hTI hIo
    exact special_flat_not_below_hyperplane s.first_indec s.first_rank s.hW s.hY hI
      s.middle_corank s.middle_decomp (fun _ ha => ⟨ha.1.1,ha.2⟩) hh.1.1 hh.2.1 hh.2.2
  obtain ⟨G,hG,hDG,hGF,hGr,hI,hIo⟩ := exists_corankFour_eligible hΓ s.D_indec s.first_indec hT
    s.D_subset_first (hb.2.1.trans hBT) s.first_rank hrT hex hno hF₁T
  let I := M.closure (G ∪ T)
  have hTI : T ⊆ I := M.subset_closure_of_subset' Set.subset_union_right hT.subset_ground
  have hspan : ∀ F, M.closure (F ∪ T) = M.E → M.closure (F ∪ I) = M.E := by
    intro F hj
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← hj]
    exact M.closure_mono (Set.union_subset_union_right F hTI)
  have hh := obs I hI hTI hIo
  exact ⟨G,I,hG,hDG,hGF,hGr,rfl,hI,hIo,hh.1,hh.2,hspan _ hF₁T,hspan _ hF₂T⟩
end TutteFormalization.Homotopy.SpecialData
