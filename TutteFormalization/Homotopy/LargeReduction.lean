import TutteFormalization.Homotopy.LargeInsertion
import TutteFormalization.Homotopy.TwoStepEdges

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Complete Case 2.3: retain the first bad vertex, preserve u, and strictly
lower v using the source's containment estimate for the raised flat F'. -/
theorem firstOffender_large_decrease (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) (p : TuttePath M) {D G : Set α}
    (hp : p.Off Γ) (hon : p.On D) (hclosed : Closed p) (hD : M.IsFlat D)
    (hG : Indecomposable M G) (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hbase : G ⊆ p.origin) (hu : 0 < outsideCount p G) (hv : 3 < firstTripleCorank p G)
    (hrD : natRank M M.E - natRank M D ≤ n+1) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G = outsideCount p G ∧
      firstTripleCorank r G < firstTripleCorank p G := by
  let i := firstOutside p G hu
  have hi := firstOutside_interior p G hu hclosed hbase
  change 0 < i.val ∧ i.val < p.length at hi
  have hk : i.val-1+2 ≤ p.length := by omega
  have h1 : i.val-1+1 = i.val := by omega
  have h2 : i.val-1+2 = i.val+1 := by omega
  let t := p.twoStep (i.val-1) hk
  have heF : t.carrier = localTriple p i.val := by
    rw [TuttePath.twoStep_carrier]
    simp only [localTriple,vertexMod_eq p (i.val-1) (by omega),
      vertexMod_eq p i.val (by omega),vertexMod_eq p (i.val+1) (by omega),h1,h2]
  have hlt : 3 < natRank M M.E - natRank M (localTriple p i.val) := by
    simpa only [firstTripleCorank,dif_pos hu] using hv
  have hle := natRank_mono (M := M) (localTriple_indec p i.val hi.1 hi.2).1.subset_ground
  have hcr : natRank M t.carrier + 4 ≤ natRank M M.E := by rw [heF]; omega
  have hbefore : G ⊆ p.vertex ⟨i.val-1,by omega⟩ :=
    before_firstOutside p G hu (by change i.val-1 < i.val; omega)
  have hbad : ¬ G ⊆ p.vertex ⟨i.val-1+1,by omega⟩ := by
    simpa only [h1,Fin.eta] using firstOutside_bad p G hu
  have het : t.carrier = t.vertex 0 ∩ t.vertex 1 ∩ t.vertex 2 := p.twoStep_carrier (i.val-1) hk
  let s : LargeCorankStep M Γ D G := {
    H := t.vertex 0, B := t.vertex 1, J := t.vertex 2
    hH := t.isHyperplane 0, hB := t.isHyperplane 1, hJ := t.isHyperplane 2
    hHB := t.adjacent ⟨0,by change 0 < 2; decide⟩
    hBJ := t.adjacent ⟨1,by change 1 < 2; decide⟩
    offH := hp _, offB := hp _, offJ := hp _
    onH := hon _, onB := hon _, onJ := hon _
    goodH := hbefore, badB := hbad, triple_rank := het ▸ hcr }
  obtain ⟨P,q,hrP,he,hqD,hcount,hlen,hgood,hbadq,hprev,hmid,hnext⟩ :=
    s.exists_insertion hM hΓ hlower hD hG hDG hrG hrD
  have hepath : t = s.path := p.twoStep_eq_edges (i.val-1) hk
  rw [← hepath] at he hcount
  have hprefix : (p.initialSegment (i.val-1) (by omega)).On G := by
    intro j
    exact before_firstOutside p G hu (by change j.val < i.val; have := j.isLt; change j.val < i.val-1+1 at this; omega)
  have hbetter : natRank M (localTriple p (firstOutside p G hu).val) < natRank M P := by
    have hsf : s.F = localTriple p i.val := het.symm.trans heF
    rw [hsf] at hrP
    change natRank M (localTriple p i.val) < natRank M P
    omega
  exact insertion_descent p (i.val-1) hk hp hon hu hprefix q he hqD hcount hlen hgood hbadq hprev hmid hnext hbetter
end TutteFormalization.Homotopy
