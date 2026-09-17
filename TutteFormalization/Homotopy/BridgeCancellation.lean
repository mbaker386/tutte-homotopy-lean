import TutteFormalization.Homotopy.BridgeDeformation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Right division in the generated path groupoid, using proved backtrack
cancellation and contextual homotopy, not a new relation constructor. -/
theorem homotopic_right_division (hΓ : ModularCut M Γ) {a b c : TuttePath M}
    (hab : a.terminus = b.origin) (h : Homotopic M Γ (a.concat b hab) c) :
    Homotopic M Γ a (c.concat b.reverse (by simpa using h.endpoints.2.symm)) := by
  have ha := TuttePath.off_of_concat_left hab h.off.1
  have hb := TuttePath.off_of_concat_right hab h.off.1
  have hbbr : b.terminus = b.reverse.origin := by simp
  have hcancel := reverse_cancel hΓ b ((off_cutPlus _).mp hb)
  have hc := hcancel.prepend a ha (by simpa using hab)
  have hc' : Homotopic M Γ (a.concat (b.concat b.reverse hbbr) (by simpa using hab)) a := by
    simpa only [NullHomotopic,TuttePath.concat_origin,
      TuttePath.concat_constant_eq a b.origin (b.isHyperplane 0) hab] using hc
  have hh := h.append b.reverse (TuttePath.reverse_off hb) (by simpa using hbbr)
  exact hc'.symm.trans (by simpa only [TuttePath.concat_assoc a b b.reverse hab hbbr] using hh)

/-- B.20's three-bridge diagram. The middle comparison loops are filled on
G₁/G₂, their common bridge cancels, and the remaining outer loop is filled on A. -/
theorem Lower.null_via_three_bridges (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    (a u v d p q r : TuttePath M)
    (hau : a.terminus = u.origin) (huv : u.terminus = v.origin)
    (hvd : v.terminus = d.origin) (hda : d.terminus = a.origin)
    (huq : u.terminus = q.origin) (hvr : v.terminus = r.origin)
    (hup : u.origin = p.origin) (hqp : q.terminus = p.terminus)
    (hvq : v.origin = q.origin) (hrq : r.terminus = q.terminus)
    (ha : a.Off Γ) (hu : u.Off Γ) (hv : v.Off Γ) (hd : d.Off Γ)
    (hp : p.Off Γ) (hq : q.Off Γ) (hr : r.Off Γ)
    {A G₁ G₂ : Set α} (haA : a.On A) (hdA : d.On A) (hpA : p.On A) (hrA : r.On A)
    (huG₁ : u.On G₁) (hqG₁ : q.On G₁) (hpG₁ : p.On G₁)
    (hvG₂ : v.On G₂) (hrG₂ : r.On G₂) (hqG₂ : q.On G₂)
    (hAr : natRank M M.E - natRank M A ≤ n)
    (hG₁r : natRank M M.E - natRank M G₁ ≤ n)
    (hG₂r : natRank M M.E - natRank M G₂ ≤ n) :
    NullHomotopic M Γ ((a.concat (u.concat v huv) hau).concat d ((TuttePath.concat_terminus a (u.concat v huv) hau).trans
      ((TuttePath.concat_terminus u v huv).trans hvd))) := by
  have h₁ := Lower.homotopic_on hΓ h (p := u.concat q huq) (q := p)
    hup (by simpa using hqp) (TuttePath.concat_off hu hq huq) hp (TuttePath.concat_on huG₁ hqG₁ huq) hpG₁ hG₁r
  have h₂ := Lower.homotopic_on hΓ h (p := v.concat r hvr) (q := q)
    hvq (by simpa using hrq) (TuttePath.concat_off hv hr hvr) hq (TuttePath.concat_on hvG₂ hrG₂ hvr) hqG₂ hG₂r
  have hmid : Homotopic M Γ ((u.concat v huv).concat r (by simpa using hvr)) p := by
    have hh := (h₂.prepend u ((off_cutPlus _).mpr hu) huv).trans h₁
    simpa only [TuttePath.concat_assoc u v r huv hvr] using hh
  have hdiv := homotopic_right_division hΓ (by simpa using hvr) hmid
  have hctx := (hdiv.prepend a ((off_cutPlus _).mpr ha) hau).append d
    ((off_cutPlus _).mpr hd) ((TuttePath.concat_terminus a (u.concat v huv) hau).trans
      ((TuttePath.concat_terminus u v huv).trans hvd))
  apply null_of_homotopic hctx
  apply h.null_of_on (D := A) (by simpa [Closed] using hda.symm)
    (TuttePath.concat_off (TuttePath.concat_off ha
      (TuttePath.concat_off hp (TuttePath.reverse_off hr) _) _) hd _)
    (TuttePath.concat_on (TuttePath.concat_on haA
      (TuttePath.concat_on hpA (TuttePath.reverse_on hrA) _) _) hdA _) hAr
end TutteFormalization.Homotopy
