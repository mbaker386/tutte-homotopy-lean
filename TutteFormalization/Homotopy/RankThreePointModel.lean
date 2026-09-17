import TutteFormalization.Homotopy.UniformRankThree
import TutteFormalization.Homotopy.RankTwoPencilModel

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Three distinct covers spanning above a corank-three flat yield an actual
Boolean rank-three model. This is the geometric input for second-kind triangles. -/
theorem exists_rankThreePointEmbedding {D : Set α} (hD : M.IsFlat D)
    (hrD : natRank M D + 3 = natRank M M.E)
    (P : Fin 3 → Set α) (hP : ∀ i, M.IsFlat (P i)) (hDP : ∀ i, D ⊆ P i)
    (hrP : ∀ i, natRank M (P i) = natRank M D + 1) (hinj : Function.Injective P)
    (hspan : M.closure ((P 0 ∪ P 1) ∪ P 2) = M.E) :
    ∃ φ : ModelEmbedding u33 M, φ.image ∅ = D ∧ ∀ i, φ.image {i} = P i := by
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
  have hspanN : (M ／ D).closure (e '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = (M ／ D).E := by
    have huniv : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
    have himage : e '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) = ({e 0} ∪ {e 1}) ∪ {e 2} := by
      simp [huniv]
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [himage]
    calc
      (M ／ D).closure (({e 0} ∪ {e 1}) ∪ {e 2}) =
          (M ／ D).closure (((M ／ D).closure {e 0} ∪ (M ／ D).closure {e 1}) ∪ (M ／ D).closure {e 2}) := by
        rw [Matroid.closure_union_closure_right_eq]
        rw [← (M ／ D).closure_union_closure_left_eq ((M ／ D).closure {e 0} ∪ (M ／ D).closure {e 1}) {e 2}]
        rw [Matroid.closure_closure_union_closure_eq_closure_union, Matroid.closure_union_closure_left_eq]
      _ = (M ／ D).closure (((P 0 \ D) ∪ (P 1 \ D)) ∪ (P 2 \ D)) := by rw [hec,hec,hec]
      _ = M.closure ((P 0 ∪ P 1) ∪ P 2) \ D := by
        rw [← Set.union_sdiff_distrib,closure_sdiff_pair_contract ((hDP 0).trans Set.subset_union_left)]
      _ = (M ／ D).E := by rw [hspan]; rfl
  let φ := (rankThreeModel e he hei hrN hspanN).liftContraction hD u33_simple.1
  refine ⟨φ,?_,?_⟩
  · change (M ／ D).closure (e '' (↑(∅ : Finset (Fin 3)) : Set (Fin 3))) ∪ D = D
    simp only [Finset.coe_empty,Set.image_empty,closure_union_contract hD,Set.empty_union,hD.closure]
  · intro i
    change (M ／ D).closure (e '' (↑({i} : Finset (Fin 3)) : Set (Fin 3))) ∪ D = P i
    simp only [Finset.coe_singleton,Set.image_singleton,hec i,Set.sdiff_union_of_subset (hDP i)]
end TutteFormalization.Homotopy
