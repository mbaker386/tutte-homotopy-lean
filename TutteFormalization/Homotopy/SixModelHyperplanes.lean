import TutteFormalization.Homotopy.RecognizedSixModel
import TutteFormalization.Homotopy.HyperplaneRecognition

namespace TutteFormalization.Homotopy.SixFlatData
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

/-- The rank table already proved from the three decomposable pair planes,
now instantiated at the actual labels chosen for the special configuration. -/
theorem representative_rank (S : Finset (Fin 6)) :
    natRank (M ／ s.D) (d.representative '' (S : Set (Fin 6))) = bipartiteModel.rank S := by
  let planes := fun j => c.planes j \ s.D
  have hp : ∀ j, IsHyperplane (M ／ s.D) (planes j) :=
    fun j => hyperplane_sdiff_contract s.D_indec.1 (c.planes_hyperplane j) (c.planes_above j)
  exact bipartite_rank_table d.representative d.representative_ground d.representative_injective
    d.contract_rank_four
    (nonCircuit_four_indep d.representative d.representative_ground d.representative_injective
      planes hp d.representative_incidence
      (d.label_pair_corank d.representative d.representative_closure)
      (d.label_pair_decomp d.representative d.representative_closure) d.contract_rank_four)
    (pair_plane_circuit_rank d.representative d.representative_ground d.representative_injective
      planes hp d.representative_incidence
      (d.label_pair_corank d.representative d.representative_closure)
      (d.label_pair_decomp d.representative d.representative_closure) d.contract_rank_four) S

/-- All indecomposable rank-one flats of the contraction are among the six
actual representative closures. This discharges the generation hypothesis. -/
theorem contracted_points_complete {P : Set α} (hP : Indecomposable (M ／ s.D) P)
    (hrP : natRank (M ／ s.D) P = 1) :
    ∃ i, P = (M ／ s.D).closure {d.representative i} := by
  have hPU : Indecomposable M (P ∪ s.D) :=
    (indecomposable_union_contract_iff s.D_indec.1 hP.1).mpr hP
  have hr := natRank_contract_add s.D P s.D_indec.1.subset_ground hP.1.subset_ground
  have hrD := c.rankD
  obtain ⟨i,hi⟩ := d.complete (P ∪ s.D) hPU Set.subset_union_right (by omega)
  refine ⟨i,?_⟩
  rw [d.representative_closure,hi,union_sdiff_eq_self hP.1.subset_ground]

include d in
theorem contract_bottom_indecomposable : Indecomposable (M ／ s.D) ∅ := by
  have hh := (indecomposable_sdiff_contract_iff s.D_indec.1 (Set.Subset.refl s.D)).mpr s.D_indec
  simpa only [Set.sdiff_self] using hh

/-- Every actual hyperplane above D is one of the eleven model hyperplanes.
Only hyperplanes are asserted here, not the entire ambient flat interval. -/
theorem hyperplanes_recognized {H : Set α} (hH : IsHyperplane M H) (hDH : s.D ⊆ H) :
    ∃ F ∈ bipartiteHyperplanes, d.ambientModel.image F = H := by
  obtain ⟨F,hF,he⟩ := fourth_hyperplanes_recognized d.representative d.representative_ground
    d.representative_rank d.contract_bottom_indecomposable d.contract_rank_four
    (fun _ hi hr => d.contracted_points_complete hi hr)
    (hyperplane_sdiff_contract s.D_indec.1 hH hDH)
  refine ⟨F,hF,?_⟩
  change (M ／ s.D).closure (d.representative '' (F : Set (Fin 6))) ∪ s.D = H
  rw [he,Set.sdiff_union_of_subset hDH]
end TutteFormalization.Homotopy.SixFlatData
