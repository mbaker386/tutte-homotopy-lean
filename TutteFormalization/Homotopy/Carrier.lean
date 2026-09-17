import TutteFormalization.Homotopy.RankTwo

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}
namespace TuttePath

theorem concat_vertex_left (p q : TuttePath M) (h : p.terminus = q.origin)
    (i : Fin (p.length + 1)) :
    (p.concat q h).vertex ⟨i.val, by change i.val < p.length + q.length + 1; omega⟩ = p.vertex i := by
  simp [concat, show i.val ≤ p.length by omega]

theorem concat_vertex_right (p q : TuttePath M) (h : p.terminus = q.origin)
    (i : Fin (q.length + 1)) :
    (p.concat q h).vertex ⟨p.length + i.val, by change p.length + i.val < p.length + q.length + 1; omega⟩ =
      q.vertex i := by
  by_cases hi : i.val = 0
  · have hv : q.vertex i = q.origin := congrArg q.vertex (Fin.ext hi)
    rw [hv, ← h]
    simp [concat,hi,terminus,Fin.last]
  · simp [concat,show ¬ p.length + i.val ≤ p.length by omega]

theorem carrier_concat (p q : TuttePath M) (h : p.terminus = q.origin) :
    (p.concat q h).carrier = p.carrier ∩ q.carrier := by
  ext e
  simp only [carrier,Set.mem_iInter,Set.mem_inter_iff]
  constructor
  · intro he
    constructor
    · intro i
      simpa only [concat_vertex_left] using he ⟨i.val, by
        change i.val < p.length + q.length + 1; omega⟩
    · intro i
      simpa only [concat_vertex_right] using he ⟨p.length+i.val, by
        change p.length+i.val < p.length+q.length+1; omega⟩
  · rintro ⟨hp,hq⟩ i
    simp only [concat]
    split
    · exact hp _
    · exact hq _

theorem carrier_subset_vertex (p : TuttePath M) (i : Fin (p.length+1)) :
    p.carrier ⊆ p.vertex i := Set.iInter_subset _ i

theorem carrier_isFlat (p : TuttePath M) : M.IsFlat p.carrier :=
  Matroid.IsFlat.iInter (fun i => (p.isHyperplane i).1)

theorem carrier_eq_origin_of_length_zero (p : TuttePath M) (hp : p.length = 0) :
    p.carrier = p.origin := by
  apply Set.Subset.antisymm (p.carrier_subset_vertex 0)
  intro e he
  apply Set.mem_iInter.mpr
  intro i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  simpa only [hi] using he

theorem carrier_eq_inter_of_length_one (p : TuttePath M) (hp : p.length = 1) :
    p.carrier = p.origin ∩ p.terminus := by
  apply Set.Subset.antisymm
    (Set.subset_inter (p.carrier_subset_vertex 0) (p.carrier_subset_vertex (Fin.last p.length)))
  intro e he
  apply Set.mem_iInter.mpr
  intro i
  have hi := i.isLt
  have hor : i = 0 ∨ i = Fin.last p.length := by
    by_cases h0 : i.val = 0
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext (by simp only [Fin.val_last]; omega))
  rcases hor with rfl | rfl
  · exact he.1
  · exact he.2

/-- B.4: induction along the path using the adjacent endpoint union obstruction.
The inherited connected-intersection result retains its A.3 fidelity qualifier. -/
theorem carrier_indecomposable [M.Finite] (p : TuttePath M) : Indecomposable M p.carrier := by
  suffices ∀ n, ∀ q : TuttePath M, q.length = n → Indecomposable M q.carrier from
    this p.length p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hq
    cases n with
    | zero =>
      rw [carrier_eq_origin_of_length_zero q hq]
      exact hyperplane_indecomposable (q.isHyperplane 0)
    | succ k =>
      obtain ⟨a,e,ha,he,hae,rfl⟩ := q.split_last k hq
      have hIa := ih k (by omega) a ha
      have hEdge : TutteAdjacent M e.origin e.terminus := by
        simpa [origin,terminus,Fin.last,he] using e.adjacent ⟨0,by omega⟩
      have hUn := Homotopy.adjacent_union_ne_ground (e.isHyperplane 0)
        (e.isHyperplane (Fin.last e.length)) hEdge
      have hsmall : a.carrier ∪ e.terminus ≠ M.E := by
        intro hu
        apply hUn
        apply Set.Subset.antisymm
          (Set.union_subset (e.isHyperplane 0).1.subset_ground
            (e.isHyperplane (Fin.last e.length)).1.subset_ground)
        rw [← hu]
        exact Set.union_subset_union
          ((a.carrier_subset_vertex (Fin.last a.length)).trans_eq hae) Set.Subset.rfl
      have hI := indecomposable_inter hIa
        (hyperplane_indecomposable (e.isHyperplane (Fin.last e.length))) hsmall
      change Indecomposable M (a.carrier ∩ e.terminus) at hI
      rw [carrier_concat,carrier_eq_inter_of_length_one e he]
      have hsub : a.carrier ⊆ e.origin :=
        (a.carrier_subset_vertex (Fin.last a.length)).trans_eq hae
      simpa only [← Set.inter_assoc,Set.inter_eq_left.mpr hsub] using hI
end TuttePath
end TutteFormalization
