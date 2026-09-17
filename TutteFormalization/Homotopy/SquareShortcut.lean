import TutteFormalization.Homotopy.TriangleExchange

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- A proved-null square identifies its two actual two-edge halves. -/
theorem square_shortcut (hΓ : ModularCut M Γ) {H K Z T : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hZ : IsHyperplane M Z) (hT : IsHyperplane M T)
    (hHK : TutteAdjacent M H K) (hKZ : TutteAdjacent M K Z)
    (hZT : TutteAdjacent M Z T) (hTH : TutteAdjacent M T H)
    (hn : NullHomotopic M Γ (TuttePath.square hH hK hZ hT hHK hKZ hZT hTH)) :
    Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl)
      ((TuttePath.edge hH hT hTH.symm).concat (TuttePath.edge hT hZ hZT.symm) rfl) := by
  let a := (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl
  let b := (TuttePath.edge hH hT hTH.symm).concat (TuttePath.edge hT hZ hZT.symm) rfl
  have he : a.concat b.reverse rfl = TuttePath.square hH hK hZ hT hHK hKZ hZT hTH := by
    apply TuttePath.ext_vertices (p := a.concat b.reverse rfl)
      (q := TuttePath.square hH hK hZ hT hHK hKZ hZT hTH) rfl
    intro i; fin_cases i <;> rfl
  exact homotopic_of_null_comparison hΓ (p := a) (q := b) rfl rfl (he.symm ▸ hn)
end TutteFormalization.Homotopy
