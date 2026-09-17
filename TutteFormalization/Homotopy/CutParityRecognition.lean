import TutteFormalization.Homotopy.CubeParity
import TutteFormalization.Homotopy.FourthCutRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

set_option maxRecDepth 100000 in
-- The 64 ordered pairs of binary triples: two common labels give a modular
-- intersection lying in one of the three pair planes.
theorem cube_intersection_geometry : ∀ i j : Fin 8, i ≠ j →
    (cubeTriple i ∩ cubeTriple j).card ≤ 1 ∨
    (bipartiteModel.rank (cubeTriple i) + bipartiteModel.rank (cubeTriple j) =
      bipartiteModel.rank (cubeTriple i ∩ cubeTriple j) +
        bipartiteModel.rank (bipartiteModel.closure (cubeTriple i ∪ cubeTriple j))) ∧
      ∃ H ∈ fourCircuits, cubeTriple i ∩ cubeTriple j ⊆ H := by decide

/-- The modular-cut obstruction in the recognition supplement: distinct cut
triples cannot agree in two coordinates, since a pair plane would enter the cut. -/
theorem cut_cube_intersection_le_one (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (offpairs : ∀ H ∈ fourCircuits, φ.image H ∉ cutPlus M Γ)
    {i j : Fin 8} (hne : i ≠ j)
    (hi : φ.image (cubeTriple i) ∈ cutPlus M Γ)
    (hj : φ.image (cubeTriple j) ∈ cutPlus M Γ) :
    (cubeTriple i ∩ cubeTriple j).card ≤ 1 := by
  rcases cube_intersection_geometry i j hne with h | ⟨hmod,H,hH,hsub⟩
  · exact h
  · have fi : bipartiteModel.Flat (cubeTriple i) :=
      (bipartite_flats _).mpr (Or.inr (Or.inl (cubeTriple_geometry i).2.1))
    have fj : bipartiteModel.Flat (cubeTriple j) :=
      (bipartite_flats _).mpr (Or.inr (Or.inl (cubeTriple_geometry j).2.1))
    have fH : bipartiteModel.Flat H := by
      have aux : ∀ H ∈ fourCircuits, bipartiteModel.Flat H := by decide
      exact aux H hH
    have hmem := φ.induced_inter hΓ ⟨fi,hi⟩ ⟨fj,hj⟩ hmod
    exact False.elim (offpairs H hH (φ.induced_upward hΓ hmem fH hsub).2)

/-- Once B.27 supplies the count four, the actual ambient cut has one parity
class of triple hyperplanes. The count is explicit and remains to be discharged. -/
theorem actual_cut_cube_parity (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (offpairs : ∀ H ∈ fourCircuits, φ.image H ∉ cutPlus M Γ)
    (C : Finset (Fin 8))
    (hC : ∀ i, i ∈ C ↔ φ.image (cubeTriple i) ∈ cutPlus M Γ)
    (hcard : C.card = 4) : C = {0,3,5,6} ∨ C = {1,2,4,7} := by
  apply four_cube_triples_parity C hcard
  intro i hi j hj hne
  exact cut_cube_intersection_le_one φ hΓ offpairs hne ((hC i).mp hi) ((hC j).mp hj)
end TutteFormalization.Homotopy
