import TutteFormalization.Homotopy.TransversalChoice

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.17 with HD-006's approved clarification: distinctness comes from opposite
pole membership FIRST; equal cover ranks then identify the intersection. -/
theorem exists_opposite_poles (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 3 ≤ n) (hlower : Lower M Γ n)
    (hrD : natRank M s.D + (n+1) = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ A B C, s.TypeA A ∧ A ⊆ s.W ∧ ¬ A ⊆ s.Y ∧ s.TypeB B ∧ s.TypeB C ∧
      A ⊆ B ∧ A ⊆ C ∧ M.closure (B ∪ s.F₁) ∉ Γ ∧ M.closure (B ∪ s.F₂) ∈ Γ ∧
      M.closure (C ∪ s.F₁) ∈ Γ ∧ M.closure (C ∪ s.F₂) ∉ Γ ∧ B ≠ C ∧ B ∩ C = A := by
  obtain ⟨A,ha,hAW,hnAY⟩ := s.exists_typeA_under_W
  have hL₁ := s.typeA_first_join ha
  have hL₂ := s.typeA_second_join ha
  have hL₁W : M.closure (A ∪ s.F₁) ⊆ s.W :=
    (M.closure_mono (Set.union_subset hAW (fun _ hf => hf.1.1))).trans_eq s.hW.1.closure
  have hL₂W : M.closure (A ∪ s.F₂) ⊆ s.W :=
    (M.closure_mono (Set.union_subset hAW Set.inter_subset_right)).trans_eq s.hW.1.closure
  obtain ⟨H,hH,hLH,hHW,hHo⟩ := exists_other_off_hyperplane hΓ hL₁.1 hL₁.2 s.hW hL₁W s.offW
  obtain ⟨K,hK,hLK,hKW,hKo⟩ := exists_other_off_hyperplane hΓ hL₂.1 hL₂.2 s.hW hL₂W s.offW
  have hAH : A ⊆ H := (M.subset_closure_of_subset' Set.subset_union_left ha.1.1.subset_ground).trans hLH
  have hAK : A ⊆ K := (M.subset_closure_of_subset' Set.subset_union_left ha.1.1.subset_ground).trans hLK
  have hF₁H : s.F₁ ⊆ H := (M.subset_closure_of_subset' Set.subset_union_right
    s.first_indec.1.subset_ground).trans hLH
  have hF₂K : s.F₂ ⊆ K := (M.subset_closure_of_subset' Set.subset_union_right
    s.second_indec.1.subset_ground).trans hLK
  obtain ⟨B,hb,hAB,hBH⟩ := s.exists_typeB_under ha hAW hnAY hH hAH hHW
  obtain ⟨C,hc,hAC,hCK⟩ := s.exists_typeB_under ha hAW hnAY hK hAK hKW
  have hB₁ : M.closure (B ∪ s.F₁) = H := pole_eq_of_containment hBH hF₁H hH (s.typeB_first_pole hb)
  have hC₂ : M.closure (C ∪ s.F₂) = K := pole_eq_of_containment hCK hF₂K hK (s.typeB_second_pole hc)
  have hoB : M.closure (B ∪ s.F₁) ∉ Γ := hB₁ ▸ hHo
  have hoC : M.closure (C ∪ s.F₂) ∉ Γ := hC₂ ▸ hKo
  have hiB := (s.pole_in_cut hM hΓ hn hlower hrD hnot hb).resolve_left hoB
  have hiC := (s.pole_in_cut hM hΓ hn hlower hrD hnot hc).resolve_right hoC
  have hBC : B ≠ C := by
    intro heq
    exact hoC (heq ▸ hiB)
  have hAr := ha.2.2.1
  have hBr := hb.2.2.1
  have hCr := hc.2.2.1
  have hmeet := cover_flats_inter_eq ha.1.1 hb.1.1 hc.1.1 hAB hAC (by omega) (by omega) hBC
  exact ⟨A,B,C,ha,hAW,hnAY,hb,hc,hAB,hAC,hoB,hiB,hiC,hoC,hBC,hmeet⟩
end TutteFormalization.Homotopy.SpecialData
