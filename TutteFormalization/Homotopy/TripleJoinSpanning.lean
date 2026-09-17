import TutteFormalization.Homotopy.FourPointEmbedding

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Two distinct hyperplane joins sharing a point force the triple to span.
This is used to discharge, not assume, the U(3,4) model's rank table. -/
theorem triple_spans_of_pair_joins {A B C H K : Set α}
    (hA : M.IsFlat A) (hB : M.IsFlat B) (hC : M.IsFlat C)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hne : H ≠ K)
    (hab : M.closure (A ∪ B) = H) (hac : M.closure (A ∪ C) = K) :
    M.closure ((A ∪ B) ∪ C) = M.E := by
  have hj := hyperplane_join_eq_ground hH hK hne
  have hs : H ∪ K ⊆ M.closure ((A ∪ B) ∪ C) := by
    apply Set.union_subset
    · rw [← hab]; exact M.closure_mono Set.subset_union_left
    · rw [← hac]
      apply M.closure_mono
      exact Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right
  apply Set.Subset.antisymm (M.closure_subset_ground _)
  rw [← hj]
  exact (M.closure_mono hs).trans_eq (M.closure_closure _)

/-- The four unordered triples suffice; permutations are literal set unions. -/
theorem four_triples_span (P : Fin 4 → Set α)
    (h012 : M.closure ((P 0 ∪ P 1) ∪ P 2) = M.E)
    (h013 : M.closure ((P 0 ∪ P 1) ∪ P 3) = M.E)
    (h023 : M.closure ((P 0 ∪ P 2) ∪ P 3) = M.E)
    (h123 : M.closure ((P 1 ∪ P 2) ∪ P 3) = M.E) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k → M.closure ((P i ∪ P j) ∪ P k) = M.E := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact False.elim (hij rfl)
    | exact False.elim (hik rfl)
    | exact False.elim (hjk rfl)
    | (apply Eq.trans ?_ h012; apply congrArg M.closure; ext x; simp only [Set.mem_union]; tauto)
    | (apply Eq.trans ?_ h013; apply congrArg M.closure; ext x; simp only [Set.mem_union]; tauto)
    | (apply Eq.trans ?_ h023; apply congrArg M.closure; ext x; simp only [Set.mem_union]; tauto)
    | (apply Eq.trans ?_ h123; apply congrArg M.closure; ext x; simp only [Set.mem_union]; tauto)
end TutteFormalization.Homotopy
