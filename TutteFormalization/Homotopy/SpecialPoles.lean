import TutteFormalization.Homotopy.SpecialData
import TutteFormalization.Homotopy.SquareReplacement

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.15, applied to a special path: at least one actual pole of every type-(b)
transversal belongs to the cut. All local geometry and replacement premises are
proved here; only the authorized same-ambient Lower premise remains. -/
theorem pole_in_cut (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 3 ≤ n) (hlower : Lower M Γ n)
    (hrD : natRank M s.D + (n+1) = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) {B : Set α} (hb : s.TypeB B) :
    M.closure (B ∪ s.F₁) ∈ Γ ∨ M.closure (B ∪ s.F₂) ∈ Γ := by
  let U := M.closure (B ∪ s.F₁)
  let V := M.closure (B ∪ s.F₂)
  have hU : IsHyperplane M U := s.typeB_first_pole hb
  have hV : IsHyperplane M V := s.typeB_second_pole hb
  have hBU : B ⊆ U := M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hBV : B ⊆ V := M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hF₁U : s.F₁ ⊆ U := M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground
  have hF₂V : s.F₂ ⊆ V := M.subset_closure_of_subset' Set.subset_union_right s.second_indec.1.subset_ground
  have hWU : s.W ≠ U := fun h => hb.2.2.2.1 (hBU.trans_eq h.symm)
  have hY U' (hBU' : B ⊆ U') : s.Y ≠ U' := fun h => hb.2.2.2.2 (hBU'.trans_eq h.symm)
  have hWV : s.W ≠ V := fun h => hb.2.2.2.1 (hBV.trans_eq h.symm)
  have edgesU := third_hyperplane_adjacent s.first_indec s.first_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.1.1,ha.2⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right hU hWU (hY U hBU) hF₁U
  have edgesV := third_hyperplane_adjacent s.second_indec s.second_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.2,ha.1.1⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right hV hWV (hY V hBV) hF₂V
  have hRF₁ : natRank M M.E - natRank M s.F₁ ≤ n := by
    have hr : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
    omega
  have hRF₂ : natRank M M.E - natRank M s.F₂ ≤ n := by
    have hr : natRank M s.F₂ + 3 = natRank M M.E := s.second_rank
    omega
  by_contra hno
  have ho : U ∉ Γ ∧ V ∉ Γ := by simpa only [not_or] using hno
  have hequiv := square_replace hΓ hlower s.hW s.hX s.hY s.hZ hU hV
    s.hWX s.hXY s.hYZ s.hZW edgesU.1.symm edgesU.2 edgesV.2.symm edgesV.1
    s.offW s.offX s.offY s.offZ ho.1 ho.2
    (show s.F₁ ⊆ s.W from fun _ ha => ha.1.1)
    (show s.F₁ ⊆ s.X from fun _ ha => ha.1.2)
    (show s.F₁ ⊆ s.Y from Set.inter_subset_right) hF₁U
    (show s.F₂ ⊆ s.W from Set.inter_subset_right)
    (show s.F₂ ⊆ s.Y from fun _ ha => ha.1.1)
    (show s.F₂ ⊆ s.Z from fun _ ha => ha.1.2) hF₂V hRF₁ hRF₂
  have hnot' : ¬ NullHomotopic M Γ
      (TuttePath.square s.hW hU s.hY hV edgesU.1.symm edgesU.2 edgesV.2.symm edgesV.1) :=
    fun hnull => hnot (null_of_homotopic hequiv hnull)
  have hi := s.typeB_intersections hb
  have hres := square_pole_obstruction hM hΓ hlower s.hW hU s.hY hV
    edgesU.1.symm edgesU.2 edgesV.2.symm edgesV.1 s.offW s.offY hb.1 hBU hBV
    (by have := hi.2.2.1; omega) (by have := hi.2.2.2.1; omega) hnot'
  exact hres.elim ho.1 ho.2
end TutteFormalization.Homotopy.SpecialData
