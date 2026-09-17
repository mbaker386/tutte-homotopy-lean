import TutteFormalization.Homotopy.CorankThreeReduction

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Apply complete Case 2.2 to an actual segment and preserve its surrounding
contexts, endpoints and On/Off conditions. -/
theorem shorten_corankThree_segment (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {D G : Set α} (hp : p.Off Γ) (hon : p.On D) (hD : M.IsFlat D)
    (hG : Indecomposable M G) (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hrF : natRank M (p.twoStep k hk).carrier + 3 = natRank M M.E)
    (hGH : G ⊆ p.vertex ⟨k,by omega⟩) (hGK : ¬ G ⊆ p.vertex ⟨k+1,by omega⟩)
    (hrD : natRank M M.E - natRank M D ≤ n+1) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let t := p.twoStep k hk
  have heF : t.carrier = t.vertex 0 ∩ t.vertex 1 ∩ t.vertex 2 := p.twoStep_carrier k hk
  let s : CorankThreeStep M Γ D G := {
    H := t.vertex 0, K := t.vertex 1, J := t.vertex 2
    hH := t.isHyperplane 0, hK := t.isHyperplane 1, hJ := t.isHyperplane 2
    hHK := t.adjacent ⟨0,by change 0 < 2; decide⟩
    hKJ := t.adjacent ⟨1,by change 1 < 2; decide⟩
    offH := hp _, offK := hp _, offJ := hp _
    onH := hon _, onK := hon _, onJ := hon _
    goodH := hGH, badK := hGK
    triple_rank := heF ▸ hrF }
  obtain ⟨q,hq,hqD,hcount⟩ := s.reduced hM hΓ hlower hD hG hDG hrG hrD
  have he : t = s.path := p.twoStep_eq_edges k hk
  rw [← he] at hq hcount
  exact replace_twoStep_decreases p k hk hp hon q hq hqD hcount

/-- Complete Case 2.2 at the first outside occurrence, retaining the source's
counting proof and all four residual cases through CorankThreeStep.reduced. -/
theorem firstOffender_corankThree_decrease (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) (p : TuttePath M) {D G : Set α}
    (hp : p.Off Γ) (hon : p.On D) (hclosed : Closed p) (hD : M.IsFlat D)
    (hG : Indecomposable M G) (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hbase : G ⊆ p.origin) (hu : 0 < outsideCount p G) (hv : firstTripleCorank p G = 3)
    (hrD : natRank M M.E - natRank M D ≤ n+1) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let i := firstOutside p G hu
  have hi := firstOutside_interior p G hu hclosed hbase
  change 0 < i.val ∧ i.val < p.length at hi
  have hk : i.val-1+2 ≤ p.length := by omega
  have h1 : i.val-1+1 = i.val := by omega
  have h2 : i.val-1+2 = i.val+1 := by omega
  have he : (p.twoStep (i.val-1) hk).carrier = localTriple p i.val := by
    rw [TuttePath.twoStep_carrier]
    simp only [localTriple,vertexMod_eq p (i.val-1) (by omega),
      vertexMod_eq p i.val (by omega),vertexMod_eq p (i.val+1) (by omega),h1,h2]
  have hr : natRank M M.E - natRank M (localTriple p i.val) = 3 := by
    simpa only [firstTripleCorank,dif_pos hu] using hv
  have hcr : natRank M (p.twoStep (i.val-1) hk).carrier + 3 = natRank M M.E := by rw [he]; omega
  have hbefore : G ⊆ p.vertex ⟨i.val-1,by omega⟩ :=
    before_firstOutside p G hu (by change i.val-1 < i.val; omega)
  have hbad : ¬ G ⊆ p.vertex ⟨i.val-1+1,by omega⟩ := by
    simpa only [h1,Fin.eta] using firstOutside_bad p G hu
  exact shorten_corankThree_segment hM hΓ hlower p (i.val-1) hk hp hon hD hG hDG hrG hcr hbefore hbad hrD
end TutteFormalization.Homotopy
