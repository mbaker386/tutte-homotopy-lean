import TutteFormalization.Homotopy.Deformation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

theorem ElementaryStep.append {p q : TuttePath M} (h : ElementaryStep M Γ p q)
    (r : TuttePath M) (hr : r.Off (cutPlus M Γ)) (hpr : p.terminus = r.origin) :
    ElementaryStep M Γ (p.concat r hpr)
      (q.concat r (h.endpoints.2.symm.trans hpr)) := by
  cases h with
  | insert a b l hab hal hl ha hb =>
    have hbr : b.terminus = r.origin := by simpa using hpr
    simpa only [insertLoop, TuttePath.concat_assoc a b r hab hbr,
      TuttePath.concat_assoc (a.concat l hal) b r _ hbr] using
      ElementaryStep.insert a (b.concat r hbr) l (by simpa using hab) hal hl ha
        (TuttePath.concat_off hb hr hbr)

theorem ElementaryStep.prepend {p q : TuttePath M} (h : ElementaryStep M Γ p q)
    (r : TuttePath M) (hr : r.Off (cutPlus M Γ)) (hrp : r.terminus = p.origin) :
    ElementaryStep M Γ (r.concat p hrp)
      (r.concat q (hrp.trans h.endpoints.1)) := by
  cases h with
  | insert a b l hab hal hl ha hb =>
    have hra : r.terminus = a.origin := by simpa using hrp
    simpa only [insertLoop, TuttePath.concat_assoc r a b hra hab,
      TuttePath.concat_assoc r a l hra hal,
      TuttePath.concat_assoc r (a.concat l hal) b (by simpa using hra)
        (by simpa using hl.closed.symm.trans (hal.symm.trans hab))] using
      ElementaryStep.insert (r.concat a hra) b l (by simpa using hab)
        (by simpa using hal) hl (TuttePath.concat_off hr ha hra) hb

theorem Homotopic.append {p q : TuttePath M} (h : Homotopic M Γ p q)
    (r : TuttePath M) (hr : r.Off (cutPlus M Γ)) (hpr : p.terminus = r.origin) :
    Homotopic M Γ (p.concat r hpr)
      (q.concat r (h.endpoints.2.symm.trans hpr)) := by
  induction h with
  | refl p hp => exact Homotopic.refl _ (TuttePath.concat_off hp hr hpr)
  | step h => exact Homotopic.step (h.append r hr hpr)
  | symm h ih => exact (ih (h.endpoints.2.trans hpr)).symm
  | trans h k ih ik => exact (ih hpr).trans (ik (h.endpoints.2.symm.trans hpr))

theorem Homotopic.prepend {p q : TuttePath M} (h : Homotopic M Γ p q)
    (r : TuttePath M) (hr : r.Off (cutPlus M Γ)) (hrp : r.terminus = p.origin) :
    Homotopic M Γ (r.concat p hrp)
      (r.concat q (hrp.trans h.endpoints.1)) := by
  induction h with
  | refl p hp => exact Homotopic.refl _ (TuttePath.concat_off hr hp hrp)
  | step h => exact Homotopic.step (h.prepend r hr hrp)
  | symm h ih => exact (ih (hrp.trans h.endpoints.1.symm)).symm
  | trans h k ih ik => exact (ih hrp).trans (ik (hrp.trans h.endpoints.1))

/-- A proved-null loop may be removed in any two off-cut matching contexts. -/
theorem null_context {a b l : TuttePath M} (h : NullHomotopic M Γ l)
    (ha : a.Off (cutPlus M Γ)) (hb : b.Off (cutPlus M Γ))
    (hab : a.terminus = b.origin) (hal : a.terminus = l.origin) :
    Homotopic M Γ (insertLoop a b l hab hal (null_closed h)) (a.concat b hab) := by
  have hp := h.prepend a ha hal
  have hq := hp.append b hb (by simpa using (null_closed h).symm.trans (hal.symm.trans hab))
  simpa only [insertLoop, TuttePath.concat_constant_eq a l.origin (l.isHyperplane 0) hal] using hq
end TutteFormalization.Homotopy
