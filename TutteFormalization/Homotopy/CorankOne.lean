import TutteFormalization.Homotopy.Carrier

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Every path whose carrier has corank at most one is constant. -/
theorem length_zero_of_carrier_corank_le_one (p : TuttePath M)
    (hr : natRank M M.E - natRank M p.carrier ≤ 1) : p.length = 0 := by
  have hc := p.carrier_isFlat
  have hcle := natRank_mono (M := M) hc.subset_ground
  have heq : ∀ i, p.carrier = p.vertex i := by
    intro i
    have hi := hyperplane_natRank (p.isHyperplane i)
    exact flat_eq_of_subset_of_natRank_le hc (p.isHyperplane i).1
      (p.carrier_subset_vertex i) (by omega)
  by_contra hn
  have hed := p.adjacent ⟨0,by omega⟩
  exact hed.1 ((heq _).symm.trans (heq _))

/-- The initial carrier-corank case in Appendix B's final induction, including
zero-edge paths and arbitrary modular cuts. -/
theorem null_of_carrier_corank_le_one {Γ : Set (Set α)} (p : TuttePath M)
    (hoff : p.Off Γ) (hr : natRank M M.E - natRank M p.carrier ≤ 1) :
    NullHomotopic M Γ p := by
  have hp := length_zero_of_carrier_corank_le_one p hr
  have heq : p = TuttePath.constant p.origin (p.isHyperplane 0) := by
    apply TuttePath.ext_vertices hp
    intro i
    exact congrArg p.vertex (Fin.ext (by have := i.isLt; omega))
  rw [heq]
  exact constant_null p.origin (p.isHyperplane 0) (hoff 0)
end TutteFormalization.Homotopy
