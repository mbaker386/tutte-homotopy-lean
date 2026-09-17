import TutteFormalization.Homotopy.FourthWordRelabelling
import TutteFormalization.Homotopy.SquareRotation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Recognition of the ORIGINAL square from the full parity cut and labelled
model. The only path operation used is the existing cyclic rotation constructor.
Geometric construction of the model and the cut count are separate obligations. -/
theorem fourth_path_elementary (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (b : Bool)
    (hcut : ExactCut φ Γ ((cubeParity b).image cubeTriple ∪ {Finset.univ}))
    (hpair : ∀ i, ¬ Indecomposable M (φ.image (labelPair i)))
    (x y : Fin 8) (hx : x ∉ cubeParity b) (hy : y ∉ cubeParity b)
    (hne : x.val % 2 ≠ y.val % 2)
    (p : TuttePath M)
    (hw : p.word = [{0,1,3,4},cubeTriple x,{0,2,3,5},cubeTriple y,{0,1,3,4}].map φ.image)
    (hclosed : Closed p) (hoff : p.Off (cutPlus M Γ)) : Elementary M Γ p := by
  obtain ⟨k,s,hC,hword⟩ := fourth_word_normalization b x y hx hy hne
  let ψ := φ.relabel (pairPermutation k s) (pairPermutation_rank k s)
  have hψcut : ExactCut ψ Γ fourthCut := φ.exactCut_relabel _ _ hcut hC
  have hψpair : ∀ i, ¬ Indecomposable M (ψ.image (labelPair i)) := by
    intro i
    obtain ⟨j,hj⟩ := pairPermutation_pairs k s i
    change ¬ Indecomposable M (φ.image ((labelPair i).image (pairPermutation k s)))
    rw [hj]
    exact hpair j
  have base : ∀ q : TuttePath M, q.word = fourthWord.map ψ.image → Closed q →
      q.Off (cutPlus M Γ) → Elementary M Γ q := by
    intro q hq hc ho
    exact Elementary.base (BaseElementary.fourth ψ q hψcut (hψpair 0) (hψpair 1)
      (hψpair 2) hq hc ho)
  rcases hword with hw0 | hw1
  · apply base p _ hclosed hoff
    rw [hw,← hw0,List.map_map]
    rfl
  · have hw' : p.word = [φ.image {0,1,3,4},φ.image (cubeTriple x),
        φ.image {0,2,3,5},φ.image (cubeTriple y),φ.image {0,1,3,4}] := by simpa using hw
    obtain ⟨a,c,hac,hca,hp,hrot⟩ := square_rotation hw'
    have ha := TuttePath.off_of_concat_left hac (hp ▸ hoff)
    have hc := TuttePath.off_of_concat_right hac (hp ▸ hoff)
    have he : Elementary M Γ (c.concat a hca) := by
      apply base _ _ (by simpa [Closed] using hac.symm) (TuttePath.concat_off hc ha hca)
      rw [hrot]
      have hh := congrArg (List.map φ.image) hw1
      simpa only [List.map_map,List.map_cons,List.map_nil,ψ,ModelEmbedding.relabel,Function.comp_def] using hh.symm
    rw [hp]
    exact Elementary.rotate hca hac hc ha he
end TutteFormalization.Homotopy
