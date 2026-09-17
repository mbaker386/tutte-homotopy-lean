import TutteFormalization.Homotopy.ContextFirstTriple

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.3's strict lexicographic descent from a proved local insertion.
The bad vertex is retained, u is unchanged, and the new triple need only
contain P: the proof uses <= corank(P), not an asserted carrier equality. -/
theorem insertion_descent (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {D G P : Set α} (hp : p.Off Γ) (hon : p.On D) (hu : 0 < outsideCount p G)
    (hprefix : (p.initialSegment k (by omega)).On G) (q : TuttePath M)
    (he : Homotopic M Γ (p.twoStep k hk) q) (hqD : q.On D)
    (hcount : outsideCount q G = outsideCount (p.twoStep k hk) G)
    (hlen : 3 ≤ q.length)
    (hgood : ∀ j : Fin (q.length+1), j.val < q.length-1 → G ⊆ q.vertex j)
    (hbad : ¬ G ⊆ q.vertex ⟨q.length-1,by omega⟩)
    (hprevP : P ⊆ q.vertex ⟨q.length-2,by omega⟩)
    (hbadP : P ⊆ q.vertex ⟨q.length-1,by omega⟩)
    (hnextP : P ⊆ q.vertex (Fin.last q.length))
    (hbetter : natRank M (localTriple p (firstOutside p G hu).val) < natRank M P) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G = outsideCount p G ∧
      firstTripleCorank r G < firstTripleCorank p G := by
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
  have hcountR : outsideCount r G = outsideCount p G := by
    have h1 := outsideCount_concat t b htb G
    have h2 := outsideCount_concat q b hqb G
    have h3 := outsideCount_concat a (t.concat b htb) (by simpa using hat) G
    have h4 := outsideCount_concat a (q.concat b hqb) (by simpa using haq) G
    conv at h4 => lhs; arg 2; rw [TuttePath.concat_origin, ← he.endpoints.1]
    conv at h3 => lhs; arg 2; rw [TuttePath.concat_origin]
    change outsideCount r G + _ = _ at h4
    rw [← hsplit] at h3
    dsimp only [t] at *
    omega
  have hpos : 0 < outsideCount r G := by rw [hcountR]; exact hu
  have hindex : (firstOutside r G hpos).val = a.length+(q.length-1) :=
    context_firstOutside a q b haq hqb G hprefix hlen hgood hbad hpos
  have hsub : P ⊆ localTriple r (firstOutside r G hpos).val := by
    rw [hindex]
    exact subset_context_localTriple a q b haq hqb hlen hprevP hbadP hnextP
  have hm := natRank_mono (M := M) hsub
  have hPE : P ⊆ M.E := hprevP.trans (q.isHyperplane _).1.subset_ground
  have hrank := natRank_mono (M := M) hPE
  refine ⟨r,hpr,TuttePath.concat_on (p.initialSegment_on k (by omega) hon)
    (TuttePath.concat_on hqD (p.finalSegment_on (k+2) hk hon) _) _,hcountR,?_⟩
  simp only [firstTripleCorank,dif_pos hpos,dif_pos hu]
  omega
end TutteFormalization.Homotopy
