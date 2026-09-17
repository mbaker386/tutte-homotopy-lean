import TutteFormalization.Homotopy.ExtraSquare

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The last deformation of the extra-flat branch: the two null comparison
squares identify both halves with one bridge, which cancels with its reverse. -/
theorem square_null_of_two_auxiliary (hΓ : ModularCut M Γ) {W X Y Z H : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hZ : IsHyperplane M Z) (hH : IsHyperplane M H)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)
    (hYH : TutteAdjacent M Y H) (hHW : TutteAdjacent M H W)
    (h₁ : NullHomotopic M Γ (TuttePath.square hW hX hY hH hWX hXY hYH hHW))
    (h₂ : NullHomotopic M Γ (TuttePath.square hW hZ hY hH hZW.symm hYZ.symm hYH hHW)) :
    NullHomotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW) := by
  let a := (TuttePath.edge hW hX hWX).concat (TuttePath.edge hX hY hXY) rfl
  let b := (TuttePath.edge hY hZ hYZ).concat (TuttePath.edge hZ hW hZW) rfl
  let e := (TuttePath.edge hW hH hHW.symm).concat (TuttePath.edge hH hY hYH.symm) rfl
  have eq₁ : a.concat e.reverse rfl = TuttePath.square hW hX hY hH hWX hXY hYH hHW := by
    apply TuttePath.ext_vertices (p := a.concat e.reverse rfl)
      (q := TuttePath.square hW hX hY hH hWX hXY hYH hHW) rfl
    intro i; fin_cases i <;> rfl
  have eq₂ : b.reverse.concat e.reverse rfl =
      TuttePath.square hW hZ hY hH hZW.symm hYZ.symm hYH hHW := by
    apply TuttePath.ext_vertices (p := b.reverse.concat e.reverse rfl)
      (q := TuttePath.square hW hZ hY hH hZW.symm hYZ.symm hYH hHW) rfl
    intro i; fin_cases i <;> rfl
  have ha : Homotopic M Γ a e := homotopic_of_null_comparison hΓ rfl rfl (eq₁.symm ▸ h₁)
  have hb : Homotopic M Γ b.reverse e := homotopic_of_null_comparison hΓ rfl rfl (eq₂.symm ▸ h₂)
  have hbOff : b.Off (cutPlus M Γ) := by
    simpa only [TuttePath.reverse_reverse] using TuttePath.reverse_off hb.off.1
  have hh := (ha.trans hb.symm).append b hbOff rfl
  have hnull : NullHomotopic M Γ (b.reverse.concat b rfl) := by
    simpa only [TuttePath.reverse_reverse] using reverse_cancel hΓ b.reverse ((off_cutPlus _).mp hb.off.1)
  have hc := null_of_homotopic hh hnull
  have eq₃ : a.concat b rfl = TuttePath.square hW hX hY hZ hWX hXY hYZ hZW :=
    (TuttePath.square_split hW hX hY hZ hWX hXY hYZ hZW).symm
  exact eq₃ ▸ hc
end TutteFormalization.Homotopy
