import TutteFormalization.Homotopy.LowerCalculus

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}
namespace TuttePath

/-- A valid four-edge closed word. Adjacency of every edge is required. -/
def square {W X Y Z : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W) : TuttePath M where
  length := 4
  vertex := ![W,X,Y,Z,W]
  isHyperplane i := by fin_cases i <;> assumption
  adjacent i := by fin_cases i <;> assumption

variable {W X Y Z : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)

theorem square_word : (square hW hX hY hZ hWX hXY hYZ hZW).word = [W,X,Y,Z,W] := by
  simp [word,square,List.ofFn_succ]

theorem square_closed : Homotopy.Closed (square hW hX hY hZ hWX hXY hYZ hZW) := rfl

theorem square_on {D : Set α} (hDW : D ⊆ W) (hDX : D ⊆ X) (hDY : D ⊆ Y) (hDZ : D ⊆ Z) :
    (square hW hX hY hZ hWX hXY hYZ hZW).On D := by
  intro i
  fin_cases i <;> assumption

theorem square_off {Γ : Set (Set α)} (hWΓ : W ∉ Γ) (hXΓ : X ∉ Γ) (hYΓ : Y ∉ Γ) (hZΓ : Z ∉ Γ) :
    (square hW hX hY hZ hWX hXY hYZ hZW).Off Γ := by
  intro i
  fin_cases i <;> assumption

theorem square_carrier : (square hW hX hY hZ hWX hXY hYZ hZW).carrier = W ∩ X ∩ Y ∩ Z := by
  ext a
  simp [carrier,square,Fin.forall_fin_succ]
  tauto
end TuttePath
end TutteFormalization
