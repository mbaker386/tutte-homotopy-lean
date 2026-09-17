import TutteFormalization.Homotopy.CorankTwoReduction
import TutteFormalization.Homotopy.MinimalLoop

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The least outside occurrence with v=2 admits a strict u decrease.
This closes both subcases of source Case 2.1 without changing the basepoint. -/
theorem firstOffender_corankTwo_decrease (hΓ : ModularCut M Γ) (p : TuttePath M)
    {D G : Set α} (hp : p.Off Γ) (hon : p.On D) (hclosed : Closed p)
    (hG : G ⊆ p.origin) (hu : 0 < outsideCount p G) (hv : firstTripleCorank p G = 2) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let i := firstOutside p G hu
  have hi := firstOutside_interior p G hu hclosed hG
  change 0 < i.val ∧ i.val < p.length at hi
  have hk : i.val-1+2 ≤ p.length := by omega
  have h1 : i.val-1+1 = i.val := by omega
  have h2 : i.val-1+2 = i.val+1 := by omega
  have he : (p.twoStep (i.val-1) hk).carrier = localTriple p i.val := by
    rw [TuttePath.twoStep_carrier]
    simp only [localTriple,vertexMod_eq p (i.val-1) (by omega),
      vertexMod_eq p i.val (by omega),vertexMod_eq p (i.val+1) (by omega),h1,h2]
  have hind := localTriple_indec p i.val hi.1 hi.2
  have hr : natRank M M.E - natRank M (localTriple p i.val) = 2 := by
    simpa only [firstTripleCorank,dif_pos hu] using hv
  have hc : CorankTwo M (p.twoStep (i.val-1) hk).carrier := by
    rw [he,corankTwo_iff_natRank hind.1]
    omega
  have hbefore : G ⊆ p.vertex ⟨i.val-1,by omega⟩ :=
    before_firstOutside p G hu (by change i.val-1 < i.val; omega)
  have hbad : ¬ G ⊆ p.vertex ⟨i.val-1+1,by omega⟩ := by
    simpa only [h1,Fin.eta] using firstOutside_bad p G hu
  exact shorten_corankTwo_segment hΓ p (i.val-1) hk hp hon hc hbefore hbad

/-- Minimal representatives with positive u cannot have v=2. -/
theorem minimal_firstTriple_ne_two (hΓ : ModularCut M Γ) {p : TuttePath M}
    {D G : Set α} (hp : p.Off Γ) (hon : p.On D) (hclosed : Closed p)
    (hG : G ⊆ p.origin) (hu : 0 < outsideCount p G)
    (hmin : ∀ r, Homotopic M Γ p r → r.On D → outsideCount p G ≤ outsideCount r G) :
    firstTripleCorank p G ≠ 2 := by
  intro hv
  obtain ⟨r,hr,hrD,hlt⟩ := firstOffender_corankTwo_decrease hΓ p hp hon hclosed hG hu hv
  exact (not_lt_of_ge (hmin r hr hrD)) hlt
end TutteFormalization.Homotopy
