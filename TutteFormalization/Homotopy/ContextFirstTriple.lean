import TutteFormalization.Homotopy.FirstOutsideIndex

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α}

/-- The first offender after a good prefix and a middle replacement with
only its final two vertices possibly outside G. -/
theorem context_firstOutside (a q b : TuttePath M) (haq : a.terminus = q.origin)
    (hqb : q.terminus = b.origin) (G : Set α) (ha : a.On G) (hlen : 3 ≤ q.length)
    (hgood : ∀ j : Fin (q.length+1), j.val < q.length-1 → G ⊆ q.vertex j)
    (hbad : ¬ G ⊆ q.vertex ⟨q.length-1,by omega⟩)
    (hpos : 0 < outsideCount (a.concat (q.concat b hqb) (by simpa using haq)) G) :
    (firstOutside (a.concat (q.concat b hqb) (by simpa using haq)) G hpos).val =
      a.length + (q.length-1) := by
  let r := a.concat (q.concat b hqb) (by simpa using haq)
  let i : Fin (r.length+1) := ⟨a.length+(q.length-1),by
    change a.length+(q.length-1) < a.length+(q.length+b.length)+1; omega⟩
  have hi : ¬ G ⊆ r.vertex i := by
    have he := TuttePath.context_vertex_middle a q b haq hqb ⟨q.length-1,by omega⟩
    exact he.symm ▸ hbad
  have hb (j : Fin (r.length+1)) (hj : j < i) : G ⊆ r.vertex j := by
    have hjv : j.val < a.length+(q.length-1) := hj
    by_cases hja : j.val ≤ a.length
    · have he := TuttePath.concat_vertex_left a (q.concat b hqb) (by simpa using haq)
        ⟨j.val,by omega⟩
      exact he.symm ▸ ha _
    · let z : Fin (q.length+1) := ⟨j.val-a.length,by omega⟩
      have hz : a.length+z.val = j.val := by dsimp [z]; omega
      have he := TuttePath.context_vertex_middle a q b haq hqb z
      have he' : r.vertex j = q.vertex z := by
        convert he using 1
        apply congrArg r.vertex; apply Fin.ext; exact hz.symm
      exact he'.symm ▸ hgood z (by dsimp [z]; omega)
  exact congrArg Fin.val (firstOutside_eq_of_prefix r G hpos i hi hb)

/-- The new local triple contains P when the last good vertex, the bad
vertex and its successor do. The index calculation retains the <= bound. -/
theorem subset_context_localTriple (a q b : TuttePath M) (haq : a.terminus = q.origin)
    (hqb : q.terminus = b.origin) (hlen : 3 ≤ q.length) {P : Set α}
    (hprev : P ⊆ q.vertex ⟨q.length-2,by omega⟩)
    (hbad : P ⊆ q.vertex ⟨q.length-1,by omega⟩)
    (hnext : P ⊆ q.vertex (Fin.last q.length)) :
    P ⊆ localTriple (a.concat (q.concat b hqb) (by simpa using haq)) (a.length+(q.length-1)) := by
  let r := a.concat (q.concat b hqb) (by simpa using haq)
  have hidx (j : Fin (q.length+1)) : vertexMod r (a.length+j.val) = q.vertex j := by
    rw [vertexMod_eq r _ (by change a.length+j.val ≤ a.length+(q.length+b.length); omega)]
    exact TuttePath.context_vertex_middle a q b haq hqb j
  have h0 : a.length+(q.length-1)-1 = a.length+(q.length-2) := by omega
  have h2 : a.length+(q.length-1)+1 = a.length+q.length := by omega
  change P ⊆ vertexMod r _ ∩ vertexMod r _ ∩ vertexMod r _
  have hlast : vertexMod r (a.length+q.length) = q.vertex (Fin.last q.length) := by
    simpa only [Fin.val_last] using hidx (Fin.last q.length)
  rw [h0,h2,hidx ⟨q.length-2,by omega⟩,hidx ⟨q.length-1,by omega⟩,hlast]
  exact Set.subset_inter (Set.subset_inter hprev hbad) hnext
end TutteFormalization.Homotopy
