import TutteFormalization.Homotopy.CutParityRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Exact full induced cut from the actual cut triples, for any number of them.
The later counting argument, not this lemma, supplies cardinality four. -/
theorem exactCubeCut (φ : ModelEmbedding bipartiteModel M)
    {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (offpairs : ∀ H ∈ fourCircuits, φ.image H ∉ cutPlus M Γ)
    (C : Finset (Fin 8)) (hC : ∀ i, i ∈ C ↔ φ.image (cubeTriple i) ∈ cutPlus M Γ) :
    ExactCut φ Γ (C.image cubeTriple ∪ {Finset.univ}) := by
  ext F
  change (bipartiteModel.Flat F ∧ φ.image F ∈ cutPlus M Γ) ↔
    F ∈ C.image cubeTriple ∪ {Finset.univ}
  constructor
  · rintro ⟨hF,hmem⟩
    rcases (bipartite_flats F).mp hF with hsmall | hplane | htop
    · obtain ⟨H,hHC,hFH,hH,_⟩ := small_bipartite_subset_pair_plane F hsmall
      have hHF : bipartiteModel.Flat H := (bipartite_flats H).mpr (Or.inr (Or.inl hH))
      exact False.elim (offpairs H hHC (φ.induced_upward hΓ ⟨hF,hmem⟩ hHF hFH).2)
    · have hc : ∀ F ∈ bipartiteHyperplanes, F ∈ fourCircuits ∨ ∃ i, cubeTriple i = F := by decide
      rcases hc F hplane with hpair | ⟨i,rfl⟩
      · exact False.elim (offpairs F hpair hmem)
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,(hC i).mpr hmem,rfl⟩)
    · subst F
      simp
  · intro hmem
    rcases Finset.mem_union.mp hmem with hm | hm
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
      exact ⟨(bipartite_flats _).mpr (Or.inr (Or.inl (cubeTriple_geometry i).2.1)),(hC i).mp hi⟩
    · have hF := Finset.mem_singleton.mp hm
      subst F
      exact ⟨bipartiteModel.top_flat,by rw [φ.map_top]; exact Or.inr rfl⟩
end TutteFormalization.Homotopy
