import TutteFormalization.Homotopy.Context

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

theorem ElementaryStep.reverse {p q : TuttePath M} (h : ElementaryStep M Γ p q) :
    ElementaryStep M Γ p.reverse q.reverse := by
  cases h with
  | insert a b l hab hal hl ha hb =>
    have hlb : l.terminus = b.origin := hl.closed.symm.trans (hal.symm.trans hab)
    have hba : b.reverse.terminus = a.reverse.origin := by simpa using hab.symm
    have hbl : b.reverse.terminus = l.reverse.origin := by simpa using hlb.symm
    have hla : l.reverse.terminus = a.reverse.origin := by simpa using hal.symm
    simpa only [insertLoop, TuttePath.reverse_concat a b hab,
      TuttePath.reverse_concat (a.concat l hal) b (by simpa using hlb),
      TuttePath.reverse_concat a l hal,
      TuttePath.concat_assoc b.reverse l.reverse a.reverse hbl hla] using
      ElementaryStep.insert b.reverse a.reverse l.reverse hba hbl (Elementary.reverse hl)
        (TuttePath.reverse_off hb) (TuttePath.reverse_off ha)

theorem Homotopic.reverse {p q : TuttePath M} (h : Homotopic M Γ p q) :
    Homotopic M Γ p.reverse q.reverse := by
  induction h with
  | refl p hp => exact Homotopic.refl _ (TuttePath.reverse_off hp)
  | step h => exact Homotopic.step h.reverse
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik

theorem null_reverse {p : TuttePath M} (h : NullHomotopic M Γ p) :
    NullHomotopic M Γ p.reverse := by
  have hc : p.terminus = p.origin := (null_closed h).symm
  have hr := h.reverse
  unfold NullHomotopic
  simpa only [TuttePath.reverse_constant p.origin (p.isHyperplane 0), TuttePath.reverse_origin, hc] using hr

theorem null_reverse_iff {p : TuttePath M} :
    NullHomotopic M Γ p.reverse ↔ NullHomotopic M Γ p :=
  ⟨fun h => by simpa only [TuttePath.reverse_reverse] using null_reverse h, null_reverse⟩
end TutteFormalization.Homotopy
