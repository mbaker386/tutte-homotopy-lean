import TutteFormalization.Homotopy.SpecialPoles

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

theorem first_pole_edges (s : SpecialData M Γ) {B : Set α} (hb : s.TypeB B) :
    TutteAdjacent M (M.closure (B ∪ s.F₁)) s.W ∧
    TutteAdjacent M (M.closure (B ∪ s.F₁)) s.Y := by
  have hBU : B ⊆ M.closure (B ∪ s.F₁) :=
    M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  exact third_hyperplane_adjacent s.first_indec s.first_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.1.1,ha.2⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right (s.typeB_first_pole hb)
    (fun h => hb.2.2.2.1 (hBU.trans_eq h.symm)) (fun h => hb.2.2.2.2 (hBU.trans_eq h.symm))
    (M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground)

theorem second_pole_edges (s : SpecialData M Γ) {B : Set α} (hb : s.TypeB B) :
    TutteAdjacent M (M.closure (B ∪ s.F₂)) s.W ∧
    TutteAdjacent M (M.closure (B ∪ s.F₂)) s.Y := by
  have hBU : B ⊆ M.closure (B ∪ s.F₂) :=
    M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  exact third_hyperplane_adjacent s.second_indec s.second_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.2,ha.1.1⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right (s.typeB_second_pole hb)
    (fun h => hb.2.2.2.1 (hBU.trans_eq h.symm)) (fun h => hb.2.2.2.2 (hBU.trans_eq h.symm))
    (M.subset_closure_of_subset' Set.subset_union_right s.second_indec.1.subset_ground)

def poleSquare (s : SpecialData M Γ) {B C : Set α} (hb : s.TypeB B) (hc : s.TypeB C) : TuttePath M :=
  TuttePath.square s.hW (s.typeB_first_pole hb) s.hY (s.typeB_second_pole hc)
    (s.first_pole_edges hb).1.symm (s.first_pole_edges hb).2
    (s.second_pole_edges hc).2.symm (s.second_pole_edges hc).1

theorem replace_poles (s : SpecialData M Γ) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 3 ≤ n) (hlower : Lower M Γ n) {B C : Set α}
    (hb : s.TypeB B) (hc : s.TypeB C)
    (hoB : M.closure (B ∪ s.F₁) ∉ Γ) (hoC : M.closure (C ∪ s.F₂) ∉ Γ) :
    Homotopic M Γ s.path (s.poleSquare hb hc) := by
  have hr₁ : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
  have hr₂ : natRank M s.F₂ + 3 = natRank M M.E := s.second_rank
  exact square_replace hΓ hlower s.hW s.hX s.hY s.hZ (s.typeB_first_pole hb) (s.typeB_second_pole hc)
    s.hWX s.hXY s.hYZ s.hZW (s.first_pole_edges hb).1.symm (s.first_pole_edges hb).2
    (s.second_pole_edges hc).2.symm (s.second_pole_edges hc).1
    s.offW s.offX s.offY s.offZ hoB hoC
    (show s.F₁ ⊆ s.W from fun _ ha => ha.1.1)
    (show s.F₁ ⊆ s.X from fun _ ha => ha.1.2) Set.inter_subset_right
    (M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground)
    (show s.F₂ ⊆ s.W from Set.inter_subset_right)
    (show s.F₂ ⊆ s.Y from fun _ ha => ha.1.1) (show s.F₂ ⊆ s.Z from fun _ ha => ha.1.2)
    (M.subset_closure_of_subset' Set.subset_union_right s.second_indec.1.subset_ground)
    (by omega) (by omega)
end TutteFormalization.Homotopy.SpecialData
