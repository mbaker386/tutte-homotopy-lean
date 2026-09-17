import TutteFormalization.Homotopy.SpecialReplacement
import TutteFormalization.Homotopy.ThreeBridgeObstruction

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.20: the first decomposable corank-two intersection for any off-cut I
containing the two opposite transversals. -/
theorem first_intersection_decomposable (s : SpecialData M Γ)
    (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ} (hn : 3 ≤ n)
    (hlower : Lower M Γ n) (hrD : natRank M s.D + (n+1) = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) {A B C I : Set α}
    (ha : s.TypeA A) (hb : s.TypeB B) (hc : s.TypeB C)
    (hAW : A ⊆ s.W) (hAB : A ⊆ B) (hAC : A ⊆ C)
    (hoB : M.closure (B ∪ s.F₁) ∉ Γ) (hoC : M.closure (C ∪ s.F₂) ∉ Γ)
    (hI : IsHyperplane M I) (hBI : B ⊆ I) (hCI : C ⊆ I) (hIo : I ∉ Γ) :
    ¬ Indecomposable M (s.Y ∩ I) ∧ CorankTwo M (s.Y ∩ I) := by
  have hnot' : ¬ NullHomotopic M Γ (s.poleSquare hb hc) :=
    fun hnull => hnot (null_of_homotopic (s.replace_poles hΓ hn hlower hb hc hoB hoC) hnull)
  have hB' := s.typeB_intersections hb
  have hC' := s.typeB_intersections hc
  have hrA := ha.2.2.1
  have hrB := hB'.2.2.2.1
  have hrC := hC'.2.2.2.1
  have hdec := three_bridge_intersection_decomposable hM hΓ hlower s.hW (s.typeB_first_pole hb)
    s.hY (s.typeB_second_pole hc) hI (s.first_pole_edges hb).1.symm (s.first_pole_edges hb).2
    (s.second_pole_edges hc).2.symm (s.second_pole_edges hc).1 s.offW hoB s.offY hoC hIo
    hb.1 hc.1 (M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground) hBI
    (M.subset_closure_of_subset' Set.subset_union_left hc.1.1.subset_ground) hCI hAW hAB hAC
    (by omega) (by omega) (by omega) hnot'
  have hYI : s.Y ≠ I := fun heq => hb.2.2.2.2 (hBI.trans_eq heq.symm)
  exact ⟨hdec,decomposable_inter_corankTwo s.hY hI hYI hdec⟩
end TutteFormalization.Homotopy.SpecialData
