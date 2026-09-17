import TutteFormalization.Homotopy.RankThreePointModel

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Transfer an actual spanning triple of covers to their selected point
representatives in the contraction. -/
theorem representative_triple_span_contract {D : Set α} {ι : Type*}
    (P : ι → Set α) (hDP : ∀ i, D ⊆ P i) (e : ι → α)
    (hec : ∀ i, (M ／ D).closure {e i} = P i \ D) (i j k : ι)
    (hspan : M.closure ((P i ∪ P j) ∪ P k) = M.E) :
    (M ／ D).closure (({e i} ∪ {e j}) ∪ {e k}) = (M ／ D).E := by
  calc
    (M ／ D).closure (({e i} ∪ {e j}) ∪ {e k}) =
        (M ／ D).closure (((M ／ D).closure {e i} ∪ (M ／ D).closure {e j}) ∪ (M ／ D).closure {e k}) := by
      rw [Matroid.closure_union_closure_right_eq]
      rw [← (M ／ D).closure_union_closure_left_eq ((M ／ D).closure {e i} ∪ (M ／ D).closure {e j}) {e k}]
      rw [Matroid.closure_closure_union_closure_eq_closure_union,Matroid.closure_union_closure_left_eq]
    _ = (M ／ D).closure (((P i \ D) ∪ (P j \ D)) ∪ (P k \ D)) := by rw [hec,hec,hec]
    _ = M.closure ((P i ∪ P j) ∪ P k) \ D := by
      rw [← Set.union_sdiff_distrib,closure_sdiff_pair_contract ((hDP i).trans Set.subset_union_left)]
    _ = (M ／ D).E := by rw [hspan]; rfl
end TutteFormalization.Homotopy
