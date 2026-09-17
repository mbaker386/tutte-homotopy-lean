import TutteFormalization.Homotopy.PairFlatGeometry

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

theorem corankTwo_sdiff_contract {D L : Set α} (hD : M.IsFlat D)
    (hL : CorankTwo M L) (hDL : D ⊆ L) : CorankTwo (M ／ D) (L \ D) := by
  apply (corankTwo_iff_natRank (flat_sdiff_contract hL.1 hDL)).mpr
  have hrL := natRank_contract_add D (L \ D) hD.subset_ground
    (Set.sdiff_subset_sdiff_left hL.1.subset_ground)
  have hrE := natRank_contract_add D (M.E \ D) hD.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset hDL] at hrL
  rw [Set.sdiff_union_of_subset hD.subset_ground] at hrE
  have hc := corankTwo_natRank hL
  change natRank (M ／ D) (L \ D) + 2 = natRank (M ／ D) (M.E \ D)
  omega

theorem closure_sdiff_pair_contract {D P Q : Set α} (hDP : D ⊆ P) :
    (M ／ D).closure ((P \ D) ∪ (Q \ D)) = M.closure (P ∪ Q) \ D := by
  rw [M.contract_closure_eq,← Set.union_sdiff_distrib,
    Set.sdiff_union_of_subset (hDP.trans Set.subset_union_left)]

namespace SixFlatData
variable {Γ : Set (Set α)} {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)
variable (e : Fin 6 → α) (he : ∀ i, (M ／ s.D).closure {e i} = d.point i \ s.D)

include he in
theorem label_pair_closure (i : Fin 3) :
    (M ／ s.D).closure (e '' (labelPair i : Set (Fin 6))) = c.pairPlane i \ s.D := by
  have hp : e '' (labelPair i : Set (Fin 6)) =
      {e ⟨i.val,by omega⟩} ∪ {e ⟨i.val+3,by omega⟩} := by
    simp [labelPair,Set.pair_comm]
  rw [hp,← (M ／ s.D).closure_closure_union_closure_eq_closure_union,he,he,
    closure_sdiff_pair_contract (d.above _),d.pair_join]

include he in
theorem label_pair_corank (i : Fin 3) :
    CorankTwo (M ／ s.D) ((M ／ s.D).closure (e '' (labelPair i : Set (Fin 6)))) := by
  rw [d.label_pair_closure e he]
  exact corankTwo_sdiff_contract s.D_indec.1 (c.pairPlane_corank i) (d.pairPlane_above i)

include he in
theorem label_pair_decomp (i : Fin 3) :
    ¬ Indecomposable (M ／ s.D) ((M ／ s.D).closure (e '' (labelPair i : Set (Fin 6)))) := by
  rw [d.label_pair_closure e he]
  intro h
  exact c.pairPlane_decomp i ((indecomposable_sdiff_contract_iff
    (c.pairPlane_corank i).1 (d.pairPlane_above i)).mp h)
end SixFlatData
end TutteFormalization.Homotopy
