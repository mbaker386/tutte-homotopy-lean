import TutteFormalization.Homotopy.Elementary

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}

/-- Full top-only cut recognition from an off-cut family covering every
proper model flat. This checks all flats, including the bottom. -/
theorem exactTopCut_of_cover (φ : ModelEmbedding N M) {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    {ι : Type*} (C : ι → Finset (Fin n)) (hC : ∀ i, N.Flat (C i))
    (hoff : ∀ i, φ.image (C i) ∉ cutPlus M Γ)
    (cover : ∀ F, N.Flat F → F ≠ Finset.univ → ∃ i, F ⊆ C i) :
    ExactCut φ Γ {Finset.univ} := by
  classical
  ext F
  change (N.Flat F ∧ φ.image F ∈ cutPlus M Γ) ↔ F ∈ ({Finset.univ} : Finset (Finset (Fin n)))
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hF,hi⟩
    by_contra hn
    obtain ⟨i,hsub⟩ := cover F hF hn
    exact hoff i (φ.induced_upward hΓ ⟨hF,hi⟩ (hC i) hsub).2
  · rintro rfl
    exact ⟨N.top_flat,by rw [φ.map_top]; exact Or.inr rfl⟩
end TutteFormalization.Homotopy
