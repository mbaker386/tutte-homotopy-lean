import TutteFormalization.Homotopy.ContractModels
import TutteFormalization.Homotopy.Deformation

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {D : Set α}

theorem Elementary.liftContraction {Γ} {p : TuttePath (M ／ D)}
    (h : Elementary (M ／ D) (contractionCut M D Γ) p) (hD : M.IsFlat D) :
    Elementary M Γ (p.liftContraction hD) := by
  induction h with
  | base h => exact Elementary.base (h.liftContraction hD)
  | reverse h ih => exact Elementary.reverse ih
  | @rotate a b hab hba ha hb h ih =>
    rw [TuttePath.liftContraction_concat] at ih ⊢
    exact Elementary.rotate _ _ (a.liftContraction_off_normalized hD ha)
      (b.liftContraction_off_normalized hD hb) ih

theorem liftContraction_insertLoop (a b l : TuttePath (M ／ D))
    (hD : M.IsFlat D) (hab : a.terminus = b.origin)
    (hal : a.terminus = l.origin) (hl : Closed l) :
    (insertLoop a b l hab hal hl).liftContraction hD =
      insertLoop (a.liftContraction hD) (b.liftContraction hD) (l.liftContraction hD)
        (congrArg (fun F => F ∪ D) hab) (congrArg (fun F => F ∪ D) hal)
        (l.liftContraction_closed hD hl) := by
  unfold insertLoop
  simp only [TuttePath.liftContraction_concat]

theorem ElementaryStep.liftContraction {Γ} {p q : TuttePath (M ／ D)}
    (h : ElementaryStep (M ／ D) (contractionCut M D Γ) p q) (hD : M.IsFlat D) :
    ElementaryStep M Γ (p.liftContraction hD) (q.liftContraction hD) := by
  cases h with
  | insert a b l hab hal hl ha hb =>
    rw [TuttePath.liftContraction_concat, liftContraction_insertLoop]
    exact ElementaryStep.insert _ _ _ _ _ (hl.liftContraction hD)
      (a.liftContraction_off_normalized hD ha) (b.liftContraction_off_normalized hD hb)

theorem Homotopic.liftContraction {Γ} {p q : TuttePath (M ／ D)}
    (h : Homotopic (M ／ D) (contractionCut M D Γ) p q) (hD : M.IsFlat D) :
    Homotopic M Γ (p.liftContraction hD) (q.liftContraction hD) := by
  induction h with
  | refl p hp => exact Homotopic.refl _ (p.liftContraction_off_normalized hD hp)
  | step h => exact Homotopic.step (h.liftContraction hD)
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik

/-- Forward lifting only: this does not transport an ambient Lower hypothesis
into a contraction, where a filling might have left the contracted flat. -/
theorem NullHomotopic.liftContraction {Γ} {p : TuttePath (M ／ D)}
    (h : NullHomotopic (M ／ D) (contractionCut M D Γ) p) (hD : M.IsFlat D) :
    NullHomotopic M Γ (p.liftContraction hD) := by
  exact Homotopic.liftContraction h hD
end TutteFormalization.Homotopy
