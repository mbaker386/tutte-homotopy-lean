import TutteFormalization.Homotopy.BridgeDeformation
import TutteFormalization.PathTheorem

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.15's actual square filling once a path between its two poles exists. -/
theorem square_null_of_bridge (hΓ : ModularCut M Γ) {n : ℕ} (h : Lower M Γ n)
    {W X Y Z F G : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)
    (hWo : W ∉ Γ) (hXo : X ∉ Γ) (hYo : Y ∉ Γ) (hZo : Z ∉ Γ)
    (e : TuttePath M) (heX : e.origin = X) (heZ : e.terminus = Z) (heo : e.Off Γ)
    (heF : e.On F) (heG : e.On G)
    (hFW : F ⊆ W) (hFX : F ⊆ X) (hFZ : F ⊆ Z)
    (hGX : G ⊆ X) (hGY : G ⊆ Y) (hGZ : G ⊆ Z)
    (hrF : natRank M M.E - natRank M F ≤ n)
    (hrG : natRank M M.E - natRank M G ≤ n) :
    NullHomotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW) := by
  let a := TuttePath.edge hW hX hWX
  let b := (TuttePath.edge hX hY hXY).concat (TuttePath.edge hY hZ hYZ) rfl
  let d := TuttePath.edge hZ hW hZW
  have ha : a.Off Γ := by intro i; fin_cases i <;> assumption
  have hb : b.Off Γ := by
    apply TuttePath.concat_off
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  have hd : d.Off Γ := by intro i; fin_cases i <;> assumption
  have haF : a.On F := by intro i; fin_cases i <;> assumption
  have hdF : d.On F := by intro i; fin_cases i <;> assumption
  have hbG : b.On G := by
    apply TuttePath.concat_on
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption
  have hn := Lower.null_via_bridge hΓ h a b d e rfl rfl rfl heX.symm heZ.symm
    ha hb hd heo haF hdF heF hbG heG hrF hrG
  have heq : TuttePath.square hW hX hY hZ hWX hXY hYZ hZW =
      (a.concat b rfl).concat d rfl := by
    apply TuttePath.ext_vertices (p := TuttePath.square hW hX hY hZ hWX hXY hYZ hZW)
      (q := (a.concat b rfl).concat d rfl) rfl
    intro i
    fin_cases i <;> rfl
  rw [heq]
  exact hn

/-- The earlier pole obstruction, using the checked path theorem and Lower,
not a recursive call to the Special Lemma or the unfinished homotopy theorem. -/
theorem square_pole_obstruction (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (h : Lower M Γ n) {W X Y Z B : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hZ : IsHyperplane M Z)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)
    (hWo : W ∉ Γ) (hYo : Y ∉ Γ)
    (hB : Indecomposable M B) (hBX : B ⊆ X) (hBZ : B ⊆ Z)
    (hrW : natRank M M.E - natRank M (B ∩ W) ≤ n)
    (hrY : natRank M M.E - natRank M (B ∩ Y) ≤ n)
    (hn : ¬ NullHomotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW)) :
    X ∈ Γ ∨ Z ∈ Γ := by
  by_contra hnot
  push_neg at hnot
  have hproper : B ≠ M.E := by
    intro heq
    exact hX.2.1 (Set.Subset.antisymm hX.1.subset_ground (heq ▸ hBX))
  obtain ⟨e,heX,heZ,heB,heo⟩ := path_theorem M hM Γ hΓ B hB hproper
    X Z hX hZ hBX hBZ hnot.1 hnot.2
  apply hn
  exact square_null_of_bridge hΓ h hW hX hY hZ hWX hXY hYZ hZW hWo hnot.1 hYo hnot.2
    e heX heZ heo (fun i => Set.inter_subset_left.trans (heB i))
    (fun i => Set.inter_subset_left.trans (heB i)) Set.inter_subset_right
    (Set.inter_subset_left.trans hBX) (Set.inter_subset_left.trans hBZ)
    (Set.inter_subset_left.trans hBX) Set.inter_subset_right (Set.inter_subset_left.trans hBZ)
    hrW hrY
end TutteFormalization.Homotopy
