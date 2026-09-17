import TutteFormalization.Homotopy.OccurrenceMeasures

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The final proof's representative satisfying (a), (b), (c). The domain may
contain infinitely many paths; both minima are attained natural values. -/
theorem exists_minimal_loop (p : TuttePath M) (hclosed : Closed p) (hoff : p.Off Γ)
    (D G : Set α) (hon : p.On D) :
    ∃ q : TuttePath M, Homotopic M Γ q p ∧ q.On D ∧ Closed q ∧ q.origin = p.origin ∧ q.Off Γ ∧
      (∀ r, Homotopic M Γ r p → r.On D → outsideCount q G ≤ outsideCount r G) ∧
      (∀ r, Homotopic M Γ r p → r.On D → outsideCount q G = outsideCount r G →
        firstTripleCorank q G ≤ firstTripleCorank r G) := by
  obtain ⟨q,hq,hmin,hv⟩ := exists_lex_min_measure
    (fun q : TuttePath M => Homotopic M Γ q p ∧ q.On D)
    (fun q => outsideCount q G) (fun q => firstTripleCorank q G)
    ⟨p,Homotopic.refl p ((off_cutPlus p).mpr hoff),hon⟩
  refine ⟨q,hq.1,hq.2,?_,hq.1.endpoints.1,(off_cutPlus q).mp hq.1.off.1,
    fun r hr hD => hmin r ⟨hr,hD⟩,fun r hr hD he => hv r ⟨hr,hD⟩ he⟩
  exact hq.1.endpoints.1.trans (hclosed.trans hq.1.endpoints.2.symm)

/-- Case 1 of the source's final induction. -/
theorem null_of_zero_outside (hΓ : ModularCut M Γ) {n : ℕ} (hlower : Lower M Γ n)
    {p q : TuttePath M} {G : Set α} (hqp : Homotopic M Γ q p) (hclosed : Closed q)
    (hzero : outsideCount q G = 0) (hrG : natRank M M.E - natRank M G ≤ n) :
    NullHomotopic M Γ p := by
  apply null_of_homotopic hqp.symm
  exact hlower.null_of_on hclosed ((off_cutPlus q).mp hqp.off.1)
    ((outsideCount_zero_iff q G).mp hzero) hrG
end TutteFormalization.Homotopy
