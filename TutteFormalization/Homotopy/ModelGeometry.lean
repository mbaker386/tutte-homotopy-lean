import TutteFormalization.Homotopy.FiniteModels

namespace TutteFormalization.Homotopy
namespace FiniteModel
variable {n : ℕ} (N : FiniteModel n)

theorem closure_eq (S : Finset (Fin n)) :
    (N.closure S : Set (Fin n)) = N.matroid.closure S := by
  ext e
  simp only [closure, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← N.rank_eq, ← N.rank_eq]
  constructor
  · intro heq
    by_contra hn
    have hr := N.matroid.eRk_insert_eq_add_one (X := (S : Set (Fin n))) ⟨by simp, hn⟩
    have hr' : natRank N.matroid (insert e S : Finset (Fin n)) =
        natRank N.matroid S + 1 := by
      rw [← cast_natRank N.matroid (insert e (S : Set (Fin n))),
        ← cast_natRank N.matroid (S : Set (Fin n))] at hr
      exact_mod_cast hr
    omega
  · intro he
    apply Nat.le_antisymm
    · have hsub : (↑(insert e S) : Set (Fin n)) ⊆ N.matroid.closure S :=
        by simpa using Set.insert_subset he (N.matroid.subset_closure _ (by simp))
      simpa only [natRank_closure] using natRank_mono (M := N.matroid) hsub
    · exact natRank_mono (by simp)

theorem flat_iff (S : Finset (Fin n)) : N.Flat S ↔ N.matroid.IsFlat (S : Set (Fin n)) := by
  rw [N.matroid.isFlat_iff_closure_eq, ← N.closure_eq]
  exact Finset.coe_inj.symm

theorem top_flat : N.Flat Finset.univ := by
  rw [N.flat_iff]
  simpa using N.matroid.ground_isFlat

theorem inter_flat {F G : Finset (Fin n)} (hF : N.Flat F) (hG : N.Flat G) :
    N.Flat (F ∩ G) := by
  rw [N.flat_iff]
  simpa using flat_inter ((N.flat_iff F).mp hF) ((N.flat_iff G).mp hG)

theorem closure_flat (S : Finset (Fin n)) : N.Flat (N.closure S) := by
  rw [N.flat_iff, N.closure_eq]
  exact N.matroid.isFlat_closure _

/-- The full finite lattice cut, including its non-hyperplane elements. -/
def IsCut (C : Finset (Finset (Fin n))) : Prop :=
  (∀ F ∈ C, N.Flat F) ∧
  (∀ F G, F ∈ C → N.Flat G → F ⊆ G → G ∈ C) ∧
  (∀ F G, F ∈ C → G ∈ C →
    N.rank F + N.rank G = N.rank (F ∩ G) + N.rank (N.closure (F ∪ G)) → F ∩ G ∈ C)
set_option synthInstance.maxSize 2048 in
set_option maxSynthPendingDepth 8 in
instance (C : Finset (Finset (Fin n))) : Decidable (N.IsCut C) :=
  by unfold IsCut; infer_instance
end FiniteModel

def bipartiteHyperplanes : Finset (Finset (Fin 6)) :=
  {{0,1,3,4}, {0,2,3,5}, {1,2,4,5},
   {0,1,2}, {0,1,5}, {0,2,4}, {0,4,5}, {1,2,3}, {1,3,5}, {2,3,4}, {3,4,5}}
def fourthCut : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,4,5}, {1,3,5}, {2,3,4}, Finset.univ}
def thirdCut : Finset (Finset (Fin 4)) := {{1,2}, {0,3}, Finset.univ}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive checks on 64 labelled edge subsets, using kernel-reduced decide only.
theorem bipartite_flats : ∀ S, bipartiteModel.Flat S ↔
    S.card ≤ 2 ∨ S ∈ bipartiteHyperplanes ∨ S = Finset.univ := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- At most 64 squared finite inputs; no native evaluation is used.
theorem fourthCut_isCut : bipartiteModel.IsCut fourthCut := by decide

set_option maxRecDepth 100000 in
theorem thirdCut_isCut : u34.IsCut thirdCut := by decide

set_option maxRecDepth 100000 in
theorem u22_flats : ∀ S, u22.Flat S ↔ S.card < 2 ∨ S = Finset.univ := by decide

set_option maxRecDepth 100000 in
theorem u23_flats : ∀ S, u23.Flat S ↔ S.card < 2 ∨ S = Finset.univ := by decide

set_option maxRecDepth 100000 in
theorem u33_flats : ∀ S, u33.Flat S ↔ S.card < 3 ∨ S = Finset.univ := by decide

set_option maxRecDepth 100000 in
theorem u34_flats : ∀ S, u34.Flat S ↔ S.card < 3 ∨ S = Finset.univ := by decide

set_option maxRecDepth 100000 in
theorem u22_cut : u22.IsCut {Finset.univ} := by decide

set_option maxRecDepth 100000 in
theorem u23_cut : u23.IsCut {Finset.univ} := by decide

set_option maxRecDepth 100000 in
theorem u33_cut : u33.IsCut {Finset.univ} := by decide

/-- The finite flat lattices are simple (empty bottom and singleton atoms).
Their ambient representations may have higher-rank bottom and atom flats. -/
theorem u22_simple : u22.Flat ∅ ∧ ∀ i, u22.Flat {i} ∧ u22.rank {i} = 1 := by decide
theorem u23_simple : u23.Flat ∅ ∧ ∀ i, u23.Flat {i} ∧ u23.rank {i} = 1 := by decide
theorem u33_simple : u33.Flat ∅ ∧ ∀ i, u33.Flat {i} ∧ u33.rank {i} = 1 := by decide
theorem u34_simple : u34.Flat ∅ ∧ ∀ i, u34.Flat {i} ∧ u34.rank {i} = 1 := by decide
theorem bipartite_simple : bipartiteModel.Flat ∅ ∧
    ∀ i, bipartiteModel.Flat {i} ∧ bipartiteModel.rank {i} = 1 := by decide

theorem model_top_ranks : u22.rank Finset.univ = 2 ∧ u23.rank Finset.univ = 2 ∧
    u33.rank Finset.univ = 3 ∧ u34.rank Finset.univ = 3 ∧
    bipartiteModel.rank Finset.univ = 4 := by decide
end TutteFormalization.Homotopy
