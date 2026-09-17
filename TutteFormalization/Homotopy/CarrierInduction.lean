import TutteFormalization.Homotopy.LargeReduction
import TutteFormalization.Homotopy.CorankThreeSegment
import TutteFormalization.Homotopy.FirstOffenderReduction
import TutteFormalization.Homotopy.FinalCoverSelection
import TutteFormalization.Homotopy.CorankOne

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Appendix B's final induction: Lower is always in the same ambient matroid.
The attained lexicographic minimum retains all four residual corank-three
cases through firstOffender_corankThree_decrease. -/
theorem null_by_carrier_induction (hM : Connected M) (hΓ : ModularCut M Γ)
    (p : TuttePath M) (hclosed : Closed p) (hoff : p.Off Γ) : NullHomotopic M Γ p := by
  classical
  generalize he : natRank M M.E - natRank M p.carrier = c
  induction c using Nat.strong_induction_on generalizing p with
  | h c ih =>
    by_cases hc : c ≤ 1
    · exact null_of_carrier_corank_le_one p hoff (by omega)
    let n := c-1
    have hn : 1 ≤ n := by omega
    have hlower : Lower M Γ n := by
      intro r hr ho hcorank
      exact ih (natRank M M.E - natRank M r.carrier) (by omega) r hr ho rfl
    have hD := p.carrier_isFlat
    have hrD := natRank_mono (M := M) hD.subset_ground
    have hsum : natRank M p.carrier + (n+1) = natRank M M.E := by omega
    obtain ⟨G,hG,hDG,hGbase,hrG,hsumG⟩ := exists_carrier_cover p n hn hsum
    have hon : p.On p.carrier := fun i => p.carrier_subset_vertex i
    obtain ⟨q,hqp,hqD,hqc,hqbase,hqo,hmin,hminv⟩ := exists_minimal_loop p hclosed hoff p.carrier G hon
    have hbase : G ⊆ q.origin := hGbase.trans_eq hqbase.symm
    by_cases hu0 : outsideCount q G = 0
    · exact null_of_zero_outside hΓ hlower hqp hqc hu0 (by omega)
    have hu : 0 < outsideCount q G := Nat.pos_of_ne_zero hu0
    have hvbound := (firstTriple_bounds q G hu hqc hbase).1
    have hrbound : natRank M M.E - natRank M p.carrier ≤ n+1 := by omega
    by_cases hv2 : firstTripleCorank q G = 2
    · obtain ⟨r,hr,hrD,hlt⟩ := firstOffender_corankTwo_decrease hΓ q hqo hqD hqc hbase hu hv2
      have hh := hmin r (hr.symm.trans hqp) hrD
      omega
    by_cases hv3 : firstTripleCorank q G = 3
    · obtain ⟨r,hr,hrD,hlt⟩ := firstOffender_corankThree_decrease hM hΓ hlower q hqo hqD hqc hD
        hG hDG.1 hrG hbase hu hv3 hrbound
      have hh := hmin r (hr.symm.trans hqp) hrD
      omega
    have hv : 3 < firstTripleCorank q G := by omega
    obtain ⟨r,hr,hrD,hcount,hlt⟩ := firstOffender_large_decrease hM hΓ hlower q hqo hqD hqc hD
      hG hDG.1 hrG hbase hu hv hrbound
    have hh := hminv r (hr.symm.trans hqp) hrD hcount.symm
    omega
end TutteFormalization.Homotopy
