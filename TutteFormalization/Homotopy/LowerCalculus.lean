import TutteFormalization.Homotopy.PathSegments

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}
namespace TuttePath

theorem on_iff_subset_carrier (p : TuttePath M) (D : Set α) : p.On D ↔ D ⊆ p.carrier := by
  simp only [On,carrier,Set.subset_iInter_iff]

theorem reverse_on {p : TuttePath M} {D : Set α} (h : p.On D) : p.reverse.On D :=
  fun i => h i.rev

theorem concat_on {p q : TuttePath M} {D : Set α} (hp : p.On D) (hq : q.On D)
    (hpq : p.terminus = q.origin) : (p.concat q hpq).On D := by
  rw [on_iff_subset_carrier,carrier_concat]
  exact Set.subset_inter ((on_iff_subset_carrier p D).mp hp) ((on_iff_subset_carrier q D).mp hq)
end TuttePath
namespace Homotopy
variable [M.Finite] {Γ : Set (Set α)}

/-- The source's “on D” estimate uses containment of D in the carrier, not equality. -/
theorem Lower.null_of_on {n : ℕ} (h : Lower M Γ n) {p : TuttePath M} {D : Set α}
    (hc : Closed p) (hoff : p.Off Γ) (hon : p.On D)
    (hr : natRank M M.E - natRank M D ≤ n) : NullHomotopic M Γ p := by
  apply h p hc hoff
  have hm := natRank_mono (M := M) ((p.on_iff_subset_carrier D).mp hon)
  omega

/-- A null comparison loop identifies its two paths. This is the cancellation
step repeatedly used in the manuscript's deformations. -/
theorem homotopic_of_null_comparison (hΓ : ModularCut M Γ) {p q : TuttePath M}
    (ho : p.origin = q.origin) (ht : p.terminus = q.terminus)
    (h : NullHomotopic M Γ (p.concat q.reverse (by simpa using ht))) : Homotopic M Γ p q := by
  have hp := TuttePath.off_of_concat_left (by simpa using ht) h.off.1
  have hqr := TuttePath.off_of_concat_right (by simpa using ht) h.off.1
  have hq : q.Off (cutPlus M Γ) := by
    simpa only [TuttePath.reverse_reverse] using TuttePath.reverse_off hqr
  have hrq : q.reverse.terminus = q.origin := by simp
  have hc : NullHomotopic M Γ (q.reverse.concat q hrq) := by
    simpa only [TuttePath.reverse_reverse] using
      reverse_cancel hΓ q.reverse ((off_cutPlus _).mp hqr)
  have hpqr : p.terminus = q.reverse.origin := by simpa using ht
  have hleft := hc.prepend p hp hpqr
  have hleft' : Homotopic M Γ (p.concat (q.reverse.concat q hrq) hpqr) p := by
    simpa only [NullHomotopic,TuttePath.concat_origin,
      TuttePath.concat_constant_eq p q.reverse.origin (q.reverse.isHyperplane 0) hpqr] using hleft
  have hright := h.append q hq (by simpa using hrq)
  have hright' : Homotopic M Γ ((p.concat q.reverse hpqr).concat q (by simpa using hrq)) q := by
    simpa only [NullHomotopic,TuttePath.concat_origin,
      TuttePath.constant_concat_eq q p.origin (p.isHyperplane 0) ho] using hright
  exact hleft'.symm.trans (by
    simpa only [TuttePath.concat_assoc p q.reverse q hpqr hrq] using hright')

/-- B.10's local replacement principle in the same ambient M, at any basepoint. -/
theorem Lower.homotopic_on (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    {p q : TuttePath M} {D : Set α} (ho : p.origin = q.origin)
    (ht : p.terminus = q.terminus) (hp : p.Off Γ) (hq : q.Off Γ)
    (hpD : p.On D) (hqD : q.On D) (hr : natRank M M.E - natRank M D ≤ n) :
    Homotopic M Γ p q := by
  apply homotopic_of_null_comparison hΓ ho ht
  exact h.null_of_on (by simpa [Closed] using ho)
    (TuttePath.concat_off hp (TuttePath.reverse_off hq) _)
    (TuttePath.concat_on hpD (TuttePath.reverse_on hqD) _) hr
/-- B.10: replace both two-edge halves using their respective smaller-corank
flats. Stated for arbitrary segments so every endpoint and On premise is explicit. -/
theorem Lower.replace_two_segments (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    {a b c d : TuttePath M} {F G : Set α}
    (hac0 : a.origin = c.origin) (hac1 : a.terminus = c.terminus)
    (hbd0 : b.origin = d.origin) (hbd1 : b.terminus = d.terminus)
    (hab : a.terminus = b.origin) (hcd : c.terminus = d.origin)
    (ha : a.Off Γ) (hb : b.Off Γ) (hc : c.Off Γ) (hd : d.Off Γ)
    (haF : a.On F) (hcF : c.On F) (hbG : b.On G) (hdG : d.On G)
    (hF : natRank M M.E - natRank M F ≤ n)
    (hG : natRank M M.E - natRank M G ≤ n) :
    Homotopic M Γ (a.concat b hab) (c.concat d hcd) := by
  have h₁ := Lower.homotopic_on hΓ h hac0 hac1 ha hc haF hcF hF
  have h₂ := Lower.homotopic_on hΓ h hbd0 hbd1 hb hd hbG hdG hG
  exact (h₁.append b ((off_cutPlus _).mpr hb) hab).trans
    (h₂.prepend c ((off_cutPlus _).mpr hc) (hac1.symm.trans hab))
end Homotopy
end TutteFormalization
