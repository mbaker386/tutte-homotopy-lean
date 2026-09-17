import TutteFormalization.Homotopy.ModelGeometry

namespace TutteFormalization.Homotopy

/-- Edges of the complete bipartite graph with parts Fin 2 and Fin 3.
The pairs (0,3), (1,4), (2,5) have their right endpoint in common. -/
def bipartiteEdge (l : Fin 2) (r : Fin 3) : Fin 6 := ⟨3 * l.val + r.val, by omega⟩

theorem bipartiteEdge_bijective : Function.Bijective
    (fun p : Fin 2 × Fin 3 => bipartiteEdge p.1 p.2) := by decide

/-- A simple cycle in a bipartite graph alternates between distinct left and
right vertices. Here it must use exactly two left vertices. -/
theorem bipartite_cycle_half_length {k : ℕ} (hk : 2 ≤ k)
    (l : Fin k → Fin 2) (hl : Function.Injective l) : k = 2 := by
  have h := Fintype.card_le_of_injective l hl
  simp only [Fintype.card_fin] at h
  omega

/-- The edge set of an alternating simple four-cycle. -/
def rectangleEdges (l : Fin 2 → Fin 2) (r : Fin 2 → Fin 3) : Finset (Fin 6) :=
  {bipartiteEdge (l 0) (r 0), bipartiteEdge (l 1) (r 0),
   bipartiteEdge (l 1) (r 1), bipartiteEdge (l 0) (r 1)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rectangles_are_fourCircuits : ∀ C : Finset (Fin 6),
    C ∈ fourCircuits ↔ ∃ l : Fin 2 → Fin 2, ∃ r : Fin 2 → Fin 3,
      Function.Injective l ∧ Function.Injective r ∧ rectangleEdges l r = C := by decide

/-- Forest criterion for K(2,3): no alternating simple cycle is contained in I.
The half-length lemma reduces all simple bipartite cycles to these rectangles. -/
def BipartiteForest (I : Finset (Fin 6)) : Prop :=
  ∀ l : Fin 2 → Fin 2, ∀ r : Fin 2 → Fin 3,
    Function.Injective l → Function.Injective r → ¬ rectangleEdges l r ⊆ I

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bipartite_forest_iff : ∀ I : Finset (Fin 6),
    BipartiteForest I ↔ bipartiteIndependent I = true := by
  unfold BipartiteForest
  decide

/-- This actual Mathlib matroid has exactly the forest-independent edge sets
of the labelled K(2,3), identifying the finite table with its cycle matroid. -/
theorem bipartite_indep_iff_forest (I : Finset (Fin 6)) :
    bipartiteModel.matroid.Indep (I : Set (Fin 6)) ↔ BipartiteForest I := by
  rw [FiniteModel.indep_iff]
  exact (bipartite_forest_iff I).symm
/-- Edge set of any alternating simple bipartite cycle, before reducing its length. -/
def alternatingCycleEdges {k : ℕ} (hk : 2 ≤ k) (l : Fin k → Fin 2)
    (r : Fin k → Fin 3) : Finset (Fin 6) :=
  Finset.univ.biUnion fun i =>
    {bipartiteEdge (l i) (r i),
      bipartiteEdge (l ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (r i)}

theorem alternating_two (l : Fin 2 → Fin 2) (r : Fin 2 → Fin 3) :
    alternatingCycleEdges (by omega) l r = rectangleEdges l r := by
  revert l r
  decide

/-- The usual no-simple-cycle criterion with unrestricted cycle length.
Distinct vertices in each part exclude closed walks with repeated vertices. -/
def BipartiteAcyclic (I : Finset (Fin 6)) : Prop :=
  ∀ k (hk : 2 ≤ k) (l : Fin k → Fin 2) (r : Fin k → Fin 3),
    Function.Injective l → Function.Injective r → ¬ alternatingCycleEdges hk l r ⊆ I

theorem acyclic_iff_forest (I : Finset (Fin 6)) : BipartiteAcyclic I ↔ BipartiteForest I := by
  constructor
  · intro h l r hl hr
    simpa only [alternating_two] using h 2 (by omega) l r hl hr
  · intro h k hk l r hl hr
    have heq := bipartite_cycle_half_length hk l hl
    subst k
    simpa only [alternating_two] using h l r hl hr

theorem bipartite_indep_iff_acyclic (I : Finset (Fin 6)) :
    bipartiteModel.matroid.Indep (I : Set (Fin 6)) ↔ BipartiteAcyclic I := by
  rw [bipartite_indep_iff_forest, acyclic_iff_forest]
end TutteFormalization.Homotopy
