import TutteFormalization.Homotopy.ModelGeometry

namespace TutteFormalization.Homotopy

/-- Binary triples choosing one label from each of (0,3), (1,4), (2,5). -/
def cubeTriple (i : Fin 8) : Finset (Fin 6) :=
  {if i.val % 2 = 0 then 0 else 3,
   if (i.val / 2) % 2 = 0 then 1 else 4,
   if (i.val / 4) % 2 = 0 then 2 else 5}

set_option maxRecDepth 100000 in
-- Exhaustive ordinary kernel decision over the eight labelled triples.
theorem cubeTriple_injective : Function.Injective cubeTriple := by decide

set_option maxRecDepth 100000 in
-- Eight finite triples, each checked against the approved graphic model.
theorem cubeTriple_geometry : ∀ i, (cubeTriple i).card = 3 ∧
    cubeTriple i ∈ bipartiteHyperplanes ∧ cubeTriple i ∉ fourCircuits := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- There are 256 subsets of the eight triples; this is kernel-reduced decide,
-- not native evaluation. This finite recognition check does not replace B.24--B.27.
theorem four_cube_triples_parity : ∀ C : Finset (Fin 8), C.card = 4 →
    (∀ i ∈ C, ∀ j ∈ C, i ≠ j → (cubeTriple i ∩ cubeTriple j).card ≤ 1) →
    C = {0,3,5,6} ∨ C = {1,2,4,7} := by decide

set_option maxRecDepth 100000 in
-- The even parity class is exactly the four approved cut hyperplanes.
theorem even_cube_cut : ({0,3,5,6} : Finset (Fin 8)).image cubeTriple ∪
    {Finset.univ} = fourthCut := by decide

set_option maxRecDepth 100000 in
-- Swapping the labels in the first pair sends odd parity to the same cut.
theorem odd_cube_cut : (({1,2,4,7} : Finset (Fin 8)).image cubeTriple).image
    (fun S => S.image (Equiv.swap (0 : Fin 6) 3)) ∪ {Finset.univ} = fourthCut := by decide
end TutteFormalization.Homotopy
