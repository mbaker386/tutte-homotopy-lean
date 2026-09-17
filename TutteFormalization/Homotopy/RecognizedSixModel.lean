import TutteFormalization.Homotopy.ContractPairGeometry
import TutteFormalization.Homotopy.ContractModels

namespace TutteFormalization.Homotopy.SixFlatData
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

noncomputable def representative (i : Fin 6) : α :=
  Classical.choose (exists_contracted_point s.D_indec.1 (d.indec i).1 (d.above i) (d.rank i))

theorem representative_mem (i : Fin 6) : d.representative i ∈ d.point i \ s.D :=
  (Classical.choose_spec (exists_contracted_point s.D_indec.1 (d.indec i).1 (d.above i) (d.rank i))).1

theorem representative_closure (i : Fin 6) :
    (M ／ s.D).closure {d.representative i} = d.point i \ s.D :=
  (Classical.choose_spec (exists_contracted_point s.D_indec.1 (d.indec i).1 (d.above i) (d.rank i))).2

theorem representative_ground (i : Fin 6) : d.representative i ∈ (M ／ s.D).E :=
  ⟨(d.indec i).1.subset_ground (d.representative_mem i).1,(d.representative_mem i).2⟩

theorem representative_injective : Function.Injective d.representative :=
  contracted_representatives_injective d.point d.above d.injective d.representative d.representative_closure

include d in
theorem contract_rank_four : natRank (M ／ s.D) (M ／ s.D).E = 4 := by
  have hr := natRank_contract_add s.D (M.E \ s.D) s.D_indec.1.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset s.D_indec.1.subset_ground] at hr
  have hd := c.rankD
  change natRank (M ／ s.D) (M.E \ s.D) = 4
  omega

theorem representative_incidence (i : Fin 6) (j : Fin 3) :
    d.representative i ∈ c.planes j \ s.D ↔ i.val % 3 ≠ j.val :=
  (contracted_point_mem_iff (d.indec i).1 (c.planes_hyperplane j).1 (d.above i)
    (c.planes_above j) (d.representative_mem i) (d.representative_closure i)).trans (d.incidence i j)

/-- The actual fourth-kind model in the contraction, constructed from ground
labels and the proved rank/circuit table of the three decomposable pair planes. -/
noncomputable def contractModel : ModelEmbedding bipartiteModel (M ／ s.D) :=
  fourthModelOfPairPlanes d.representative d.representative_ground d.representative_injective
    (fun j => c.planes j \ s.D)
    (fun j => hyperplane_sdiff_contract s.D_indec.1 (c.planes_hyperplane j) (c.planes_above j))
    d.representative_incidence (d.label_pair_corank d.representative d.representative_closure)
    (d.label_pair_decomp d.representative d.representative_closure) d.contract_rank_four

theorem contractModel_image (S : Finset (Fin 6)) :
    d.contractModel.image S = (M ／ s.D).closure (d.representative '' (S : Set (Fin 6))) := rfl

/-- Lift the recognized model back to the original ambient matroid; no Lower
hypothesis is transported to the contraction. -/
noncomputable def ambientModel : ModelEmbedding bipartiteModel M :=
  d.contractModel.liftContraction s.D_indec.1 (by decide)

theorem ambientModel_image (S : Finset (Fin 6)) :
    d.ambientModel.image S = M.closure ((d.representative '' (S : Set (Fin 6))) ∪ s.D) :=
  closure_union_contract s.D_indec.1 _

theorem ambientModel_singleton (i : Fin 6) : d.ambientModel.image {i} = d.point i := by
  change (M ／ s.D).closure (d.representative '' (↑({i} : Finset (Fin 6)) : Set (Fin 6))) ∪ s.D = _
  simp only [Finset.coe_singleton,Set.image_singleton,d.representative_closure,
    Set.sdiff_union_of_subset (d.above i)]

theorem ambientModel_pair (i : Fin 3) : d.ambientModel.image (labelPair i) = c.pairPlane i := by
  change (M ／ s.D).closure (d.representative '' (labelPair i : Set (Fin 6))) ∪ s.D = _
  rw [d.label_pair_closure d.representative d.representative_closure,
    Set.sdiff_union_of_subset (d.pairPlane_above i)]
end TutteFormalization.Homotopy.SixFlatData
