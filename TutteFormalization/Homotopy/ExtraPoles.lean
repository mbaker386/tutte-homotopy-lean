import TutteFormalization.Homotopy.FourTransversals

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)

include c in
/-- The extra-flat branch: a new corank-three flat on W∩Y has an off-cut
pole whenever a distinct such flat supplies the known cut pole. -/
theorem extra_pole_off (hΓ : ModularCut M Γ) {P Q B : Set α}
    (hP : Indecomposable M P) (hQ : Indecomposable M Q)
    (hrP : natRank M P + 3 = natRank M M.E)
    (hrQ : natRank M Q + 3 = natRank M M.E)
    (hDP : s.D ⊆ P) (hDQ : s.D ⊆ Q)
    (hPL : P ⊆ s.W ∩ s.Y) (hQL : Q ⊆ s.W ∩ s.Y) (hPQ : P ≠ Q)
    (hb : s.TypeB B) (hcut : M.closure (B ∪ P) ∈ Γ) :
    M.closure (B ∪ Q) ∉ Γ := by
  have pole {R : Set α} (hR : Indecomposable M R)
      (hrR : natRank M R + 3 = natRank M M.E) (hDR : s.D ⊆ R) (hRL : R ⊆ s.W ∩ s.Y) :
      IsHyperplane M (M.closure (B ∪ R)) :=
    transversal_two_join_hyperplane hR hrR s.middle_corank s.middle_decomp hRL
      s.hW s.hY s.W_ne_Y Set.inter_subset_left Set.inter_subset_right
      hb.1.1 hb.2.1 hDR hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
  have hU := pole hP hrP hDP hPL
  have hV := pole hQ hrQ hDQ hQL
  have hBU : B ⊆ M.closure (B ∪ P) :=
    M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hBV : B ⊆ M.closure (B ∪ Q) :=
    M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hcB : CorankTwo M B := (corankTwo_iff_natRank hb.1.1).mpr (by
    have := c.rankD; have := hb.2.2.1; omega)
  intro hcutQ
  have he := cut_hyperplanes_unique_above hΓ hcB c.hT (c.typeB_below_T hb) c.offT
    hU hV hBU hBV hcut hcutQ
  have hrL := corankTwo_natRank s.middle_corank
  have hrD := c.rankD
  have hj : M.closure (P ∪ Q) = s.W ∩ s.Y :=
    cover_flats_join_eq s.middle_corank.1 hP.1 hQ.1 hPL hQL
      (by omega : natRank M P = natRank M s.D + 1) (by omega) (by omega) hPQ
  have hPU : P ⊆ M.closure (B ∪ P) :=
    M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have hQU : Q ⊆ M.closure (B ∪ P) :=
    (M.subset_closure_of_subset' Set.subset_union_right hQ.1.subset_ground).trans_eq he.symm
  have hLU : s.W ∩ s.Y ⊆ M.closure (B ∪ P) := hj ▸
    (M.closure_mono (Set.union_subset hPU hQU)).trans_eq hU.1.closure
  rcases (separation_hyperplanes s.hW s.hY s.middle_decomp).2 _ hU hLU with heW | heY
  · exact hb.2.2.2.1 (hBU.trans_eq heW)
  · exact hb.2.2.2.2 (hBU.trans_eq heY)

/-- A third indecomposable corank-three flat cannot lie in T; this supplies
all distinctness premises in the source's extra-flat pole construction. -/
theorem extra_not_below_T {Q : Set α} (hQ : Indecomposable M Q)
    (hrQ : natRank M Q + 3 = natRank M M.E) (hQL : Q ⊆ s.W ∩ s.Y) : ¬ Q ⊆ c.T :=
  special_flat_not_below_hyperplane hQ hrQ s.hW s.hY c.hT s.middle_corank s.middle_decomp
    hQL c.decompWT c.decompYT c.corankYT
end TutteFormalization.Homotopy.CountingFrame
