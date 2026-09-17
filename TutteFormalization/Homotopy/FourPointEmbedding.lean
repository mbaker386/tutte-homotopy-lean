import TutteFormalization.Homotopy.UniformFourPoints
import TutteFormalization.Homotopy.RepresentativeTriples

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Actual U(3,4) embedding above a corank-three flat. Every spanning-triple
premise must be supplied by the geometric configuration at its application. -/
theorem exists_fourPointEmbedding {D : Set α} (hD : M.IsFlat D)
    (hrD : natRank M D + 3 = natRank M M.E)
    (P : Fin 4 → Set α) (hP : ∀ i, M.IsFlat (P i)) (hDP : ∀ i, D ⊆ P i)
    (hrP : ∀ i, natRank M (P i) = natRank M D + 1) (hinj : Function.Injective P)
    (hspan : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → M.closure ((P i ∪ P j) ∪ P k) = M.E) :
    ∃ φ : ModelEmbedding u34 M, φ.image ∅ = D ∧ ∀ i, φ.image {i} = P i := by
  classical
  have reps (i) := exists_contracted_point hD (hP i) (hDP i) (hrP i)
  choose e hem hec using reps
  have he (i) : e i ∈ (M ／ D).E := ⟨(hP i).subset_ground (hem i).1,(hem i).2⟩
  have hei : Function.Injective e := contracted_representatives_injective P hDP hinj e hec
  have hrN : natRank (M ／ D) (M ／ D).E = 3 := by
    have hh := natRank_contract_add D (M.E \ D) hD.subset_ground Set.Subset.rfl
    rw [Set.sdiff_union_of_subset hD.subset_ground] at hh
    change natRank (M ／ D) (M.E \ D) = 3
    omega
  have hspanN (S : Finset (Fin 4)) (hS : S.card = 3) :
      (M ／ D).closure (e '' (S : Set (Fin 4))) = (M ／ D).E := by
    obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp hS
    have himage : e '' (↑({i,j,k} : Finset (Fin 4)) : Set (Fin 4)) = ({e i} ∪ {e j}) ∪ {e k} := by
      simp
      ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    rw [himage]
    exact representative_triple_span_contract P hDP e hec i j k (hspan i j k hij hik hjk)
  let φ := (rankFourPointsModel e he hei hrN hspanN).liftContraction hD u34_simple.1
  refine ⟨φ,?_,?_⟩
  · change (M ／ D).closure (e '' (↑(∅ : Finset (Fin 4)) : Set (Fin 4))) ∪ D = D
    simp only [Finset.coe_empty,Set.image_empty,closure_union_contract hD,Set.empty_union,hD.closure]
  · intro i
    change (M ／ D).closure (e '' (↑({i} : Finset (Fin 4)) : Set (Fin 4))) ∪ D = P i
    simp only [Finset.coe_singleton,Set.image_singleton,hec i,Set.sdiff_union_of_subset (hDP i)]
end TutteFormalization.Homotopy
