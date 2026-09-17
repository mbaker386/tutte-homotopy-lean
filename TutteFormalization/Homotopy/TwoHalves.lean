import TutteFormalization.Homotopy.SquareReplacement
import TutteFormalization.Homotopy.BridgeDeformation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.23's final two fillings, using a common bridge between the opposite
vertices. This is the displayed insertion/cancellation argument in contextual form. -/
theorem Lower.null_of_two_halves (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    (a b e : TuttePath M) (hab : a.terminus = b.origin) (hba : b.terminus = a.origin)
    (hae0 : a.origin = e.origin) (hae1 : a.terminus = e.terminus)
    (ha : a.Off Γ) (hb : b.Off Γ) (he : e.Off Γ)
    {F G : Set α} (haF : a.On F) (heF : e.On F) (hbG : b.On G) (heG : e.On G)
    (hrF : natRank M M.E - natRank M F ≤ n)
    (hrG : natRank M M.E - natRank M G ≤ n) : NullHomotopic M Γ (a.concat b hab) := by
  have hh := Lower.homotopic_on hΓ h hae0 hae1 ha he haF heF hrF
  apply null_of_homotopic (hh.append b ((off_cutPlus _).mpr hb) hab)
  exact h.null_of_on (by simpa [Closed] using (hba.trans hae0).symm)
    (TuttePath.concat_off he hb _) (TuttePath.concat_on heG hbG _) hrG
end TutteFormalization.Homotopy
