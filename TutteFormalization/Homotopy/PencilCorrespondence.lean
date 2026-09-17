import TutteFormalization.Homotopy.CountingPencils

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)

/-- B.26 identifies the Diamond-chosen transversal with the actual trace H∩T. -/
theorem pencil_inter_typeB {A H : Set α} (ha : s.TypeA A)
    (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y) (hH : IsHyperplane M H)
    (hLH : M.closure (A ∪ s.F₁) ⊆ H) (hHW : H ≠ s.W) :
    s.TypeB (H ∩ c.T) ∧ A ⊆ H ∩ c.T := by
  have hAH : A ⊆ H := (M.subset_closure_of_subset' Set.subset_union_left ha.1.1.subset_ground).trans hLH
  have hF₁H : s.F₁ ⊆ H := (M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground).trans hLH
  have hHT : H ≠ c.T := fun heq => c.first_not_below_T (hF₁H.trans_eq heq)
  obtain ⟨B,hb,hAB,hBH⟩ := c.exists_typeB_in_pencil ha hAW hnAY hH hAH hHW
  have hcB : CorankTwo M B := (corankTwo_iff_natRank hb.1.1).mpr (by
    have := hb.2.2.1; have := c.rankD; omega)
  have heq := hyperplane_inter_eq_of_corankTwo hcB hH c.hT hHT hBH (c.typeB_below_T hb)
  exact ⟨heq ▸ hb,heq ▸ hAB⟩

theorem pencil_first_pole {A H : Set α} (ha : s.TypeA A)
    (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y) (hH : IsHyperplane M H)
    (hLH : M.closure (A ∪ s.F₁) ⊆ H) (hHW : H ≠ s.W) :
    M.closure ((H ∩ c.T) ∪ s.F₁) = H := by
  have hb := (c.pencil_inter_typeB ha hAW hnAY hH hLH hHW).1
  exact SpecialData.pole_eq_of_containment Set.inter_subset_left
    ((M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground).trans hLH)
    hH (s.typeB_first_pole hb)

/-- Every type-(b) transversal is recovered from either of its poles by trace on T. -/
theorem first_pole_trace {B : Set α} (hb : s.TypeB B) :
    M.closure (B ∪ s.F₁) ∩ c.T = B := by
  have hcB : CorankTwo M B := (corankTwo_iff_natRank hb.1.1).mpr (by
    have := hb.2.2.1; have := c.rankD; omega)
  have hF : s.F₁ ⊆ M.closure (B ∪ s.F₁) :=
    M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground
  exact hyperplane_inter_eq_of_corankTwo hcB (s.typeB_first_pole hb) c.hT
    (fun heq => c.first_not_below_T (hF.trans_eq heq))
    (M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground) (c.typeB_below_T hb)

theorem second_pole_trace {B : Set α} (hb : s.TypeB B) :
    M.closure (B ∪ s.F₂) ∩ c.T = B := by
  have hcB : CorankTwo M B := (corankTwo_iff_natRank hb.1.1).mpr (by
    have := hb.2.2.1; have := c.rankD; omega)
  have hF : s.F₂ ⊆ M.closure (B ∪ s.F₂) :=
    M.subset_closure_of_subset' Set.subset_union_right s.second_indec.1.subset_ground
  exact hyperplane_inter_eq_of_corankTwo hcB (s.typeB_second_pole hb) c.hT
    (fun heq => c.second_not_below_T (hF.trans_eq heq))
    (M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground) (c.typeB_below_T hb)
end TutteFormalization.Homotopy.CountingFrame
