import TutteFormalization.Homotopy.LargeSpecialBridge

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Rotate the filled special square into the source's three-edge insertion
by comparison and reverse cancellation, retaining its bad endpoint. -/
theorem square_insertion (hΓ : ModularCut M Γ) {H T U B : Set α}
    (hH : IsHyperplane M H) (hT : IsHyperplane M T) (hU : IsHyperplane M U) (hB : IsHyperplane M B)
    (hHT : TutteAdjacent M H T) (hTU : TutteAdjacent M T U)
    (hUB : TutteAdjacent M U B) (hHB : TutteAdjacent M H B)
    (hn : NullHomotopic M Γ (TuttePath.square hT hU hB hH hTU hUB hHB.symm hHT)) :
    Homotopic M Γ (TuttePath.edge hH hB hHB)
      ((TuttePath.edge hH hT hHT).concat
        ((TuttePath.edge hT hU hTU).concat (TuttePath.edge hU hB hUB) rfl) rfl) := by
  let a := TuttePath.edge hH hT hHT
  let b := (TuttePath.edge hT hU hTU).concat (TuttePath.edge hU hB hUB) rfl
  let e := TuttePath.edge hH hB hHB
  have hh : Homotopic M Γ b (a.reverse.concat e rfl) := by
    have hs := square_shortcut hΓ hT hU hB hH hTU hUB hHB.symm hHT hn
    have heq : (TuttePath.edge hT hH hHT.symm).concat (TuttePath.edge hH hB hHB) rfl = a.reverse.concat e rfl := by
      apply TuttePath.eq_of_word_eq
      rfl
    exact heq ▸ hs
  have haOff : a.Off (cutPlus M Γ) := by
    have hr := TuttePath.off_of_concat_left rfl hh.off.2
    simpa only [TuttePath.reverse_reverse] using TuttePath.reverse_off hr
  have heOff : e.Off (cutPlus M Γ) := TuttePath.off_of_concat_right rfl hh.off.2
  have hc := (reverse_cancel hΓ a ((off_cutPlus a).mp haOff)).append e heOff rfl
  have hc' : Homotopic M Γ (a.concat (a.reverse.concat e rfl) rfl) e := by
    have heq := TuttePath.concat_assoc a a.reverse e rfl rfl
    have heq2 : (TuttePath.constant a.origin (a.isHyperplane 0)).concat e rfl = e := TuttePath.constant_concat e
    have hc0 : Homotopic M Γ ((a.concat a.reverse rfl).concat e rfl)
        ((TuttePath.constant a.origin (a.isHyperplane 0)).concat e rfl) := hc
    rw [heq2] at hc0
    exact heq ▸ hc0
  exact ((hh.prepend a haOff rfl).trans hc').symm
end TutteFormalization.Homotopy
