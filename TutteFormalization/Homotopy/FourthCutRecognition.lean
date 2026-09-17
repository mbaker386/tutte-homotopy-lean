import TutteFormalization.Homotopy.Elementary

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

set_option maxRecDepth 100000 in
-- Sixty-four subsets; every selected rank-at-most-two flat is below an off-cut pair plane.
theorem small_bipartite_subset_pair_plane : ∀ S : Finset (Fin 6), S.card ≤ 2 →
    ∃ H ∈ fourCircuits, S ⊆ H ∧ H ∈ bipartiteHyperplanes ∧ H ∉ fourthCut := by decide

/-- Full induced-cut recognition, not just agreement on hyperplanes. The small
flats are excluded by upward closure into an off-cut pair plane. -/
theorem exactFourthCut_of_hyperplanes (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (hplanes : ∀ H ∈ bipartiteHyperplanes,
      φ.image H ∈ cutPlus M Γ ↔ H ∈ fourthCut) : ExactCut φ Γ fourthCut := by
  ext F
  change (bipartiteModel.Flat F ∧ φ.image F ∈ cutPlus M Γ) ↔ F ∈ fourthCut
  constructor
  · rintro ⟨hF,hmem⟩
    rcases (bipartite_flats F).mp hF with hsmall | hplane | htop
    · obtain ⟨H,hHC,hFH,hH,hnot⟩ := small_bipartite_subset_pair_plane F hsmall
      have hHF : bipartiteModel.Flat H := (bipartite_flats H).mpr (Or.inr (Or.inl hH))
      have hHmem := (φ.induced_upward hΓ ⟨hF,hmem⟩ hHF hFH).2
      exact False.elim (hnot ((hplanes H hH).mp hHmem))
    · exact (hplanes F hplane).mp hmem
    · subst F
      decide
  · intro hmem
    have hF := fourthCut_isCut.1 F hmem
    refine ⟨hF,?_⟩
    have hcases : ∀ F ∈ fourthCut, F ∈ bipartiteHyperplanes ∨ F = Finset.univ := by decide
    rcases hcases F hmem with hplane | htop
    · exact (hplanes F hplane).mpr hmem
    · subst F
      rw [φ.map_top]
      exact Or.inr rfl
end TutteFormalization.Homotopy
