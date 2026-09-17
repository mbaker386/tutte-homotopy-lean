import TutteFormalization.Homotopy.SquarePaths

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}
namespace TuttePath

theorem edge_on {H K D : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (he : TutteAdjacent M H K) (hDH : D ⊆ H) (hDK : D ⊆ K) : (edge hH hK he).On D := by
  intro i; fin_cases i <;> assumption

theorem edge_off {H K : Set α} {Γ : Set (Set α)} (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (he : TutteAdjacent M H K) (hoH : H ∉ Γ) (hoK : K ∉ Γ) : (edge hH hK he).Off Γ := by
  intro i; fin_cases i <;> assumption

theorem square_split {W X Y Z : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W) :
    square hW hX hY hZ hWX hXY hYZ hZW =
      ((edge hW hX hWX).concat (edge hX hY hXY) rfl).concat
        ((edge hY hZ hYZ).concat (edge hZ hW hZW) rfl) rfl := by
  apply ext_vertices (p := square hW hX hY hZ hWX hXY hYZ hZW)
    (q := ((edge hW hX hWX).concat (edge hX hY hXY) rfl).concat
      ((edge hY hZ hYZ).concat (edge hZ hW hZW) rfl) rfl) rfl
  intro i; fin_cases i <;> rfl
end TuttePath
namespace Homotopy
variable [M.Finite] {Γ : Set (Set α)}

theorem square_replace (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    {W X Y Z X' Z' F G : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hX' : IsHyperplane M X') (hZ' : IsHyperplane M Z')
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)
    (hWX' : TutteAdjacent M W X') (hX'Y : TutteAdjacent M X' Y)
    (hYZ' : TutteAdjacent M Y Z') (hZ'W : TutteAdjacent M Z' W)
    (hWo : W ∉ Γ) (hXo : X ∉ Γ) (hYo : Y ∉ Γ) (hZo : Z ∉ Γ)
    (hX'o : X' ∉ Γ) (hZ'o : Z' ∉ Γ)
    (hFW : F ⊆ W) (hFX : F ⊆ X) (hFY : F ⊆ Y) (hFX' : F ⊆ X')
    (hGW : G ⊆ W) (hGY : G ⊆ Y) (hGZ : G ⊆ Z) (hGZ' : G ⊆ Z')
    (hrF : natRank M M.E - natRank M F ≤ n)
    (hrG : natRank M M.E - natRank M G ≤ n) :
    Homotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW)
      (TuttePath.square hW hX' hY hZ' hWX' hX'Y hYZ' hZ'W) := by
  rw [TuttePath.square_split,TuttePath.square_split]
  apply Lower.replace_two_segments hΓ h (F := F) (G := G)
    (a := (TuttePath.edge hW hX hWX).concat (TuttePath.edge hX hY hXY) rfl)
    (b := (TuttePath.edge hY hZ hYZ).concat (TuttePath.edge hZ hW hZW) rfl)
    (c := (TuttePath.edge hW hX' hWX').concat (TuttePath.edge hX' hY hX'Y) rfl)
    (d := (TuttePath.edge hY hZ' hYZ').concat (TuttePath.edge hZ' hW hZ'W) rfl)
    rfl rfl rfl rfl rfl rfl
  · exact TuttePath.concat_off (TuttePath.edge_off _ _ _ hWo hXo) (TuttePath.edge_off _ _ _ hXo hYo) _
  · exact TuttePath.concat_off (TuttePath.edge_off _ _ _ hYo hZo) (TuttePath.edge_off _ _ _ hZo hWo) _
  · exact TuttePath.concat_off (TuttePath.edge_off _ _ _ hWo hX'o) (TuttePath.edge_off _ _ _ hX'o hYo) _
  · exact TuttePath.concat_off (TuttePath.edge_off _ _ _ hYo hZ'o) (TuttePath.edge_off _ _ _ hZ'o hWo) _
  · exact TuttePath.concat_on (TuttePath.edge_on _ _ _ hFW hFX) (TuttePath.edge_on _ _ _ hFX hFY) _
  · exact TuttePath.concat_on (TuttePath.edge_on _ _ _ hFW hFX') (TuttePath.edge_on _ _ _ hFX' hFY) _
  · exact TuttePath.concat_on (TuttePath.edge_on _ _ _ hGY hGZ) (TuttePath.edge_on _ _ _ hGZ hGW) _
  · exact TuttePath.concat_on (TuttePath.edge_on _ _ _ hGY hGZ') (TuttePath.edge_on _ _ _ hGZ' hGW) _
  · exact hrF
  · exact hrG
end Homotopy
end TutteFormalization
