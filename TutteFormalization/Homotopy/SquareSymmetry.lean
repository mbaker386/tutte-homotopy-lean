import TutteFormalization.Homotopy.SquareReplacement
import TutteFormalization.Homotopy.Rotation

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

theorem square_swap_null_iff (hΓ : ModularCut M Γ) {W X Y Z : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W) :
    NullHomotopic M Γ (TuttePath.square hY hX hW hZ hXY.symm hWX.symm hZW.symm hYZ.symm) ↔
    NullHomotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW) := by
  let a := (TuttePath.edge hW hX hWX).concat (TuttePath.edge hX hY hXY) rfl
  let b := (TuttePath.edge hY hZ hYZ).concat (TuttePath.edge hZ hW hZW) rfl
  have heq : (TuttePath.square hY hX hW hZ hXY.symm hWX.symm hZW.symm hYZ.symm).reverse =
      b.concat a rfl := by
    apply TuttePath.ext_vertices
      (p := (TuttePath.square hY hX hW hZ hXY.symm hWX.symm hZW.symm hYZ.symm).reverse)
      (q := b.concat a rfl) rfl
    intro i; fin_cases i <;> rfl
  rw [← null_reverse_iff,heq,null_rotate_iff hΓ b a rfl rfl]
  rw [TuttePath.square_split]
end TutteFormalization.Homotopy
