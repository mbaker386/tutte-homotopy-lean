import TutteFormalization.Homotopy.SegmentContexts
import TutteFormalization.Homotopy.OccurrenceCounts

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- A strict local occurrence decrease survives both unchanged contexts.
The replacement itself supplies all adjacency, endpoint, On and Off facts. -/
theorem replace_twoStep_decreases (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {D G : Set α} (hp : p.Off Γ) (hon : p.On D) (q : TuttePath M)
    (he : Homotopic M Γ (p.twoStep k hk) q) (hqD : q.On D)
    (hcount : outsideCount q G < outsideCount (p.twoStep k hk) G) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let a := p.initialSegment k (by omega)
  let b := p.finalSegment (k+2) hk
  let t := p.twoStep k hk
  have htb : t.terminus = b.origin := rfl
  have hat : a.terminus = t.origin := rfl
  have hqb : q.terminus = b.origin := he.endpoints.2.symm.trans htb
  have haq : a.terminus = q.origin := hat.trans he.endpoints.1
  let r := a.concat (q.concat b hqb) (by simpa using haq)
  have hsplit : p = a.concat (t.concat b htb) (by simpa using hat) := p.split_twoStep k hk
  have hh := (he.append b ((off_cutPlus b).mpr (p.finalSegment_off (k+2) hk hp)) htb).prepend
    a ((off_cutPlus a).mpr (p.initialSegment_off k (by omega) hp)) (by simpa using hat)
  have hpr : Homotopic M Γ p r := by rw [hsplit]; exact hh
  refine ⟨r,hpr,TuttePath.concat_on (p.initialSegment_on k (by omega) hon)
    (TuttePath.concat_on hqD (p.finalSegment_on (k+2) hk hon) _) _,?_⟩
  have h1 := outsideCount_concat t b htb G
  have h2 := outsideCount_concat q b hqb G
  have h3 := outsideCount_concat a (t.concat b htb) (by simpa using hat) G
  have h4 := outsideCount_concat a (q.concat b hqb) (by simpa using haq) G
  conv at h4 => lhs; arg 2; rw [TuttePath.concat_origin, ← he.endpoints.1]
  conv at h3 => lhs; arg 2; rw [TuttePath.concat_origin]
  change outsideCount r G + _ = _ at h4
  rw [← hsplit] at h3
  change outsideCount q G < outsideCount t G at hcount
  dsimp only [t] at *
  omega
end TutteFormalization.Homotopy
