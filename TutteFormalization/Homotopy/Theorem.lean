import TutteFormalization.Homotopy.CarrierInduction

namespace TutteFormalization
/-- Current long-manuscript homotopy theorem, interpreted under authorized S1–S5.
Proved by the Appendix B carrier induction, counting argument and residual cases. -/
theorem homotopy_theorem {α : Type*} (M : Matroid α) [M.Finite]
    (hM : Connected M) (Γ : Set (Set α)) (hΓ : ModularCut M Γ)
    (p : TuttePath M) (hclosed : Homotopy.Closed p) (hoff : p.Off Γ) :
    Homotopy.NullHomotopic M Γ p := by
  exact Homotopy.null_by_carrier_induction hM hΓ p hclosed hoff
end TutteFormalization
