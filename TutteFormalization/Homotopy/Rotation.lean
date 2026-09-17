import TutteFormalization.Homotopy.Cancellation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Cyclic change of basepoint, derived from contextual moves and backtracks. -/
theorem null_rotate (hΓ : ModularCut M Γ) (a b : TuttePath M)
    (hab : a.terminus = b.origin) (hba : b.terminus = a.origin)
    (h : NullHomotopic M Γ (a.concat b hab)) :
    NullHomotopic M Γ (b.concat a hba) := by
  have ho := (off_cutPlus _).mp h.off.1
  have ha := TuttePath.off_of_concat_left hab ho
  have hb := TuttePath.off_of_concat_right hab ho
  have har := TuttePath.reverse_off ha
  have hra : a.reverse.terminus = a.origin := by simp
  have hcancel : NullHomotopic M Γ (a.reverse.concat a hra) := by
    simpa only [TuttePath.reverse_reverse] using reverse_cancel hΓ a.reverse har
  have hc := null_context h ((off_cutPlus _).mpr har) ((off_cutPlus _).mpr ha)
    hra (by simpa using hra)
  have hab2 : a.terminus = (b.concat a hba).origin := by simpa using hab
  have hcancel' : Homotopic M Γ (a.reverse.concat a hra)
      (TuttePath.constant b.origin (b.isHyperplane 0)) := by
    simpa only [NullHomotopic, TuttePath.concat_origin, TuttePath.reverse_origin, hab] using hcancel
  have hc' := hcancel'.append (b.concat a hba)
    ((off_cutPlus _).mpr (TuttePath.concat_off hb ha hba)) (by simpa using hab)
  have hfinal : Homotopic M Γ (b.concat a hba) (a.reverse.concat a hra) := by
    have heq := hc'.symm
    simp only [TuttePath.constant_concat_eq (b.concat a hba) b.origin
      (b.isHyperplane 0) rfl] at heq
    apply heq.trans
    simpa only [insertLoop,
      TuttePath.concat_assoc a.reverse a (b.concat a hba) hra hab2,
      TuttePath.concat_assoc a.reverse (a.concat b hab) a (by simpa using hra)
        (by simpa using hba),
      TuttePath.concat_assoc a b a hab hba] using hc
  simpa only [NullHomotopic, TuttePath.concat_origin] using hfinal.trans hcancel'

theorem null_rotate_iff (hΓ : ModularCut M Γ) (a b : TuttePath M)
    (hab : a.terminus = b.origin) (hba : b.terminus = a.origin) :
    NullHomotopic M Γ (a.concat b hab) ↔ NullHomotopic M Γ (b.concat a hba) :=
  ⟨null_rotate hΓ a b hab hba, null_rotate hΓ b a hba hab⟩
end TutteFormalization.Homotopy
