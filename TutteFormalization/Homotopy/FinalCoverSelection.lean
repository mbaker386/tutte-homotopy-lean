import TutteFormalization.Homotopy.MinimalLoop

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The Chain choice at the beginning of the final induction. The cover is
inside the actual basepoint hyperplane and has the requested corank. -/
theorem exists_carrier_cover (p : TuttePath M) (n : ℕ) (hn : 1 ≤ n)
    (hr : natRank M p.carrier + (n+1) = natRank M M.E) :
    ∃ G, Indecomposable M G ∧ p.carrier ⊂ G ∧ G ⊆ p.origin ∧
      natRank M G = natRank M p.carrier + 1 ∧ natRank M G + n = natRank M M.E := by
  have hH := p.isHyperplane 0
  have hHr := hyperplane_natRank hH
  obtain ⟨G,hG,hDG,hGH,hGr⟩ := exists_indecomposable_of_rank
    (hyperplane_indecomposable hH) p.carrier_indecomposable
    (p.carrier_subset_vertex 0) (natRank M p.carrier+1) (by omega) (by omega)
  refine ⟨G,hG,Set.ssubset_iff_subset_ne.mpr ⟨hDG,?_⟩,hGH,hGr,by omega⟩
  intro he
  have hh := congrArg (natRank M) he
  omega
end TutteFormalization.Homotopy
