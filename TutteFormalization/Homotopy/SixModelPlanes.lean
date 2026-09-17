import TutteFormalization.Homotopy.SixModelHyperplanes
import TutteFormalization.Homotopy.ModelRankFacts

namespace TutteFormalization.Homotopy.SixFlatData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

theorem ambientModel_bottom : d.ambientModel.image ∅ = s.D := by
  rw [d.ambientModel_image]
  simp only [Finset.coe_empty,Set.image_empty,Set.empty_union,s.D_indec.1.closure]

theorem ambientModel_above (F : Finset (Fin 6)) : s.D ⊆ d.ambientModel.image F := by
  rw [d.ambientModel_image]
  exact M.subset_closure_of_subset' Set.subset_union_right s.D_indec.1.subset_ground

theorem model_hyperplane {F : Finset (Fin 6)} (hF : F ∈ bipartiteHyperplanes) :
    IsHyperplane M (d.ambientModel.image F) := by
  have hf : ∀ F ∈ bipartiteHyperplanes, bipartiteModel.Flat F ∧
      bipartiteModel.rank F + 1 = bipartiteModel.rank Finset.univ := by decide
  exact d.ambientModel.image_hyperplane (hf F hF).1 (hf F hF).2

/-- Each model pair-plane is the actual off hyperplane excluding that label pair. -/
theorem circuit_plane {F : Finset (Fin 6)} (hF : F ∈ fourCircuits) :
    ∃ j, d.ambientModel.image F = c.planes j := by
  obtain ⟨hcard,j,hj⟩ := circuit_missing_pair F hF
  have hFH : F ∈ bipartiteHyperplanes := by
    have hh : ∀ F ∈ fourCircuits, F ∈ bipartiteHyperplanes := by decide
    exact hh F hF
  have hsub : d.ambientModel.image F ⊆ c.planes j := by
    rw [d.ambientModel_image]
    apply (M.closure_mono (Set.union_subset ?_ (c.planes_above j))).trans_eq (c.planes_hyperplane j).1.closure
    rintro _ ⟨i,hi,rfl⟩
    exact ((d.representative_incidence i j).mpr (hj i hi)).1
  have he := flat_eq_of_subset_of_natRank_le (d.model_hyperplane hFH).1 (c.planes_hyperplane j).1 hsub
    (by have := hyperplane_natRank (d.model_hyperplane hFH)
        have := hyperplane_natRank (c.planes_hyperplane j); omega)
  exact ⟨j,he⟩

theorem circuit_off {F : Finset (Fin 6)} (hF : F ∈ fourCircuits) :
    d.ambientModel.image F ∉ cutPlus M Γ := by
  obtain ⟨j,he⟩ := d.circuit_plane hF
  rw [he]
  exact (hyperplane_off_cutPlus (c.planes_hyperplane j)).mpr (c.planes_off j)
end TutteFormalization.Homotopy.SixFlatData
