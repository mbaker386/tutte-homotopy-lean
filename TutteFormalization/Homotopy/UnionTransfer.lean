import TutteFormalization.Homotopy.SpecialEdges

namespace TutteFormalization.Homotopy
variable {α : Type*}

/-- B.23's element argument transferring a non-cover across a common trace on I. -/
theorem noncover_of_same_trace {E W I X Z : Set α}
    (hX : X ⊆ E) (hW : W ⊆ E) (hWI : W ∪ I = E)
    (htrace : I ∩ X = I ∩ Z) (hn : X ∪ W ≠ E) : Z ∪ W ≠ E := by
  intro hZW
  have hnot : ¬ E ⊆ X ∪ W := fun h => hn (Set.Subset.antisymm (Set.union_subset hX hW) h)
  obtain ⟨e,heE,he⟩ := Set.not_subset.mp hnot
  have heW : e ∉ W := fun h => he (Or.inr h)
  have heI : e ∈ I := (show e ∈ W ∪ I from hWI.symm ▸ heE).resolve_left heW
  have heZ : e ∈ Z := (show e ∈ Z ∪ W from hZW.symm ▸ heE).resolve_right heW
  have heX : e ∈ X := (show e ∈ I ∩ X from htrace.symm ▸ And.intro heI heZ).2
  exact he (Or.inl heX)
end TutteFormalization.Homotopy
