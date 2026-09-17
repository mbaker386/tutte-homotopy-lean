import TutteFormalization.Homotopy.UniformRankTwo
import TutteFormalization.Homotopy.ContractPairGeometry
import TutteFormalization.Homotopy.ContractModels
import TutteFormalization.HyperplaneTools

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Actual U(2,3) recognition for three distinct hyperplanes on a corank-two
flat, with the full ambient singleton images and bottom identified. -/
theorem exists_rankTwoPencilEmbedding {D : Set α} (hD : CorankTwo M D)
    (H : Fin 3 → Set α) (hH : ∀ i, IsHyperplane M (H i))
    (hDH : ∀ i, D ⊆ H i) (hinj : Function.Injective H) :
    ∃ φ : ModelEmbedding u23 M, φ.image ∅ = D ∧ ∀ i, φ.image {i} = H i := by
  classical
  have hrD := corankTwo_natRank hD
  have reps (i : Fin 3) : ∃ e, e ∈ H i \ D ∧ (M ／ D).closure {e} = H i \ D := by
    have hr := hyperplane_natRank (hH i)
    exact exists_contracted_point hD.1 (hH i).1 (hDH i) (by omega)
  choose e hem hec using reps
  have he (i) : e i ∈ (M ／ D).E := ⟨(hH i).1.subset_ground (hem i).1,(hem i).2⟩
  have hrN : natRank (M ／ D) (M ／ D).E = 2 := by
    have hh := natRank_contract_add D (M.E \ D) hD.1.subset_ground Set.Subset.rfl
    rw [Set.sdiff_union_of_subset hD.1.subset_ground] at hh
    change natRank (M ／ D) (M.E \ D) = 2
    omega
  have hs (i) : natRank (M ／ D) {e i} = 1 := by
    rw [← natRank_closure (M ／ D) _,hec i]
    have hh := natRank_contract_add D (H i \ D) hD.1.subset_ground
      (Set.sdiff_subset_sdiff_left (hH i).1.subset_ground)
    rw [Set.sdiff_union_of_subset (hDH i)] at hh
    have hi := hyperplane_natRank (hH i)
    omega
  have hp (i j : Fin 3) (hne : i ≠ j) : (M ／ D).closure {e i,e j} = (M ／ D).E := by
    rw [show ({e i,e j} : Set α) = {e i} ∪ {e j} by simp only [Set.singleton_union],
      ← (M ／ D).closure_closure_union_closure_eq_closure_union,hec i,hec j,
      closure_sdiff_pair_contract (hDH i),hyperplane_join_eq_ground (hH i) (hH j) (fun hh => hne (hinj hh))]
    rfl
  let φ := (rankTwoModel e he hrN hs hp).liftContraction hD.1 u23_simple.1
  refine ⟨φ,?_,?_⟩
  · change (M ／ D).closure (e '' (↑(∅ : Finset (Fin 3)) : Set (Fin 3))) ∪ D = D
    simp only [Finset.coe_empty,Set.image_empty,closure_union_contract hD.1,Set.empty_union,hD.1.closure]
  · intro i
    change (M ／ D).closure (e '' (↑({i} : Finset (Fin 3)) : Set (Fin 3))) ∪ D = H i
    simp only [Finset.coe_singleton,Set.image_singleton,hec i,Set.sdiff_union_of_subset (hDH i)]
end TutteFormalization.Homotopy
