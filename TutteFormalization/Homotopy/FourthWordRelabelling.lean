import TutteFormalization.Homotopy.CubeParity
import TutteFormalization.Homotopy.PairPlaneRecognition
import TutteFormalization.Homotopy.ModelRelabelling

namespace TutteFormalization.Homotopy

/-- Independent pair flips and optional exchange of the last two pairs. -/
def pairPermutation (k : Fin 8) (s : Bool) : Equiv.Perm (Fin 6) :=
  (if s then (Equiv.swap 1 2).trans (Equiv.swap 4 5) else Equiv.refl _).trans
    ((if k.val % 2 = 0 then Equiv.refl _ else Equiv.swap 0 3).trans
    ((if (k.val / 2) % 2 = 0 then Equiv.refl _ else Equiv.swap 1 4).trans
      (if (k.val / 4) % 2 = 0 then Equiv.refl _ else Equiv.swap 2 5)))

def cubeParity (b : Bool) : Finset (Fin 8) := if b then {0,3,5,6} else {1,2,4,7}

def fourthWord : List (Finset (Fin 6)) :=
  [{0,1,3,4},{0,1,5},{0,2,3,5},{3,4,5},{0,1,3,4}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Sixteen explicit permutations on 64 subsets; ordinary kernel decision.
theorem pairPermutation_rank : ∀ k s (F : Finset (Fin 6)),
    bipartiteModel.rank (F.image (pairPermutation k s)) = bipartiteModel.rank F := by decide

set_option maxRecDepth 100000 in
-- Pair flips and exchange carry the three designated pairs to themselves.
theorem pairPermutation_pairs : ∀ k s i, ∃ j,
    (labelPair i).image (pairPermutation k s) = labelPair j := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The two parity classes and 64 ordered triple pairs. This checks the original
-- five-term word, up to the approved cyclic rotation, not just its carrier.
theorem fourth_word_normalization : ∀ b (x y : Fin 8), x ∉ cubeParity b →
    y ∉ cubeParity b → x.val % 2 ≠ y.val % 2 →
    ∃ k s, fourthCut.image (fun F => F.image (pairPermutation k s)) =
        (cubeParity b).image cubeTriple ∪ {Finset.univ} ∧
      ((fourthWord.map (fun F => F.image (pairPermutation k s)) =
          [{0,1,3,4},cubeTriple x,{0,2,3,5},cubeTriple y,{0,1,3,4}]) ∨
       (fourthWord.map (fun F => F.image (pairPermutation k s)) =
          [{0,2,3,5},cubeTriple y,{0,1,3,4},cubeTriple x,{0,2,3,5}])) := by decide
end TutteFormalization.Homotopy
