import TutteFormalization.Homotopy.CorankThreeSegment

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α}

/-- Identify the least outside occurrence from a bad index and an on-G prefix. -/
theorem firstOutside_eq_of_prefix (p : TuttePath M) (G : Set α) (h : 0 < outsideCount p G)
    (i : Fin (p.length+1)) (hi : ¬ G ⊆ p.vertex i)
    (hbefore : ∀ j, j < i → G ⊆ p.vertex j) : firstOutside p G h = i := by
  have hle : firstOutside p G h ≤ i := Finset.min'_le _ _ (mem_outsideIndices.mpr hi)
  apply le_antisymm hle
  by_contra hn
  exact firstOutside_bad p G h (hbefore _ (lt_of_not_ge hn))
end TutteFormalization.Homotopy

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

/-- Exact vertex lookup in the middle component of a contextual replacement. -/
theorem context_vertex_middle (a q b : TuttePath M) (haq : a.terminus = q.origin)
    (hqb : q.terminus = b.origin) (j : Fin (q.length+1)) :
    (a.concat (q.concat b hqb) (by simpa using haq)).vertex
      ⟨a.length+j.val,by change a.length+j.val < a.length+(q.length+b.length)+1; omega⟩ = q.vertex j := by
  have h1 := concat_vertex_right a (q.concat b hqb) (by simpa using haq)
    (⟨j.val,by change j.val < q.length+b.length+1; omega⟩ : Fin ((q.concat b hqb).length+1))
  have h2 := concat_vertex_left q b hqb j
  exact h1.trans h2
end TutteFormalization.TuttePath
