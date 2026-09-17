import TutteFormalization.Homotopy.SquarePaths

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

theorem null_of_homotopic {p q : TuttePath M} (h : Homotopic M Γ p q)
    (hq : NullHomotopic M Γ q) : NullHomotopic M Γ p := by
  have ht := h.trans hq
  simpa only [NullHomotopic,← h.endpoints.1] using ht

/-- B.15's deformation diagram: replace the middle segment on G by a bridge,
then fill the resulting closed path on F. Both fillings use the same Lower. -/
theorem Lower.null_via_bridge (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    (a b d e : TuttePath M)
    (hab : a.terminus = b.origin) (hbd : b.terminus = d.origin)
    (hda : d.terminus = a.origin)
    (hbe0 : b.origin = e.origin) (hbe1 : b.terminus = e.terminus)
    (ha : a.Off Γ) (hb : b.Off Γ) (hd : d.Off Γ) (he : e.Off Γ)
    {F G : Set α} (haF : a.On F) (hdF : d.On F) (heF : e.On F)
    (hbG : b.On G) (heG : e.On G)
    (hF : natRank M M.E - natRank M F ≤ n)
    (hG : natRank M M.E - natRank M G ≤ n) :
    NullHomotopic M Γ ((a.concat b hab).concat d (by simpa using hbd)) := by
  have hcomp := Lower.homotopic_on hΓ h hbe0 hbe1 hb he hbG heG hG
  have hcontext := (hcomp.prepend a ((off_cutPlus _).mpr ha) hab).append d
    ((off_cutPlus _).mpr hd) (by simpa using hbd)
  apply null_of_homotopic hcontext
  apply h.null_of_on (D := F) (by simpa [Closed] using hda.symm)
    (TuttePath.concat_off (TuttePath.concat_off ha he _) hd _)
    (TuttePath.concat_on (TuttePath.concat_on haF heF _) hdF _) hF
end TutteFormalization.Homotopy
