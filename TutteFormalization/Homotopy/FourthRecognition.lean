import TutteFormalization.Homotopy.FullCubeCut
import TutteFormalization.Homotopy.FourthPathRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Conditional recognition at B.28: after constructing the actual labelled
model and proving its count four, the original ambient square is elementary.
The count and geometric premises are explicit obligations for the counting proof. -/
theorem fourth_elementary_of_count (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (offpairs : ∀ H ∈ fourCircuits, φ.image H ∉ cutPlus M Γ)
    (hpair : ∀ i, ¬ Indecomposable M (φ.image (labelPair i)))
    (C : Finset (Fin 8)) (hC : ∀ i, i ∈ C ↔ φ.image (cubeTriple i) ∈ cutPlus M Γ)
    (hcard : C.card = 4) (x y : Fin 8) (hne : x.val % 2 ≠ y.val % 2)
    (p : TuttePath M)
    (hw : p.word = [{0,1,3,4},cubeTriple x,{0,2,3,5},cubeTriple y,{0,1,3,4}].map φ.image)
    (hclosed : Closed p) (hoff : p.Off (cutPlus M Γ)) : Elementary M Γ p := by
  have hx : x ∉ C := by
    intro hx
    exact (TuttePath.off_of_mem_word hoff (H := φ.image (cubeTriple x)) (by rw [hw]; simp))
      ((hC x).mp hx)
  have hy : y ∉ C := by
    intro hy
    exact (TuttePath.off_of_mem_word hoff (H := φ.image (cubeTriple y)) (by rw [hw]; simp))
      ((hC y).mp hy)
  have hcut := exactCubeCut φ hΓ offpairs C hC
  rcases actual_cut_cube_parity φ hΓ offpairs C hC hcard with h | h
  · subst C
    exact fourth_path_elementary φ true hcut hpair x y hx hy hne p hw hclosed hoff
  · subst C
    exact fourth_path_elementary φ false hcut hpair x y hx hy hne p hw hclosed hoff
end TutteFormalization.Homotopy
