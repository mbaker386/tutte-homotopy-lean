import TutteFormalization.Homotopy.Embedding

namespace TutteFormalization.Homotopy.ModelEmbedding
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}

/-- Relative ranks and preservation of top identify model hyperplanes in M. -/
theorem image_hyperplane (φ : ModelEmbedding N M) {F : Finset (Fin n)}
    (hF : N.Flat F) (hrF : N.rank F + 1 = N.rank Finset.univ) :
    IsHyperplane M (φ.image F) := by
  apply isHyperplane_of_natRank (φ.image_flat F hF)
  have hf := φ.relative_rank F hF
  have ht := φ.top_rank
  omega
end TutteFormalization.Homotopy.ModelEmbedding
