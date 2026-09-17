import TutteFormalization.Homotopy.BridgeCancellation
import TutteFormalization.Homotopy.SquareReplacement
import TutteFormalization.PathTheorem

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.20's Y∩I obstruction. The three paths are obtained from the checked path
 theorem; the source's three-bridge deformation is performed in ambient M. -/
theorem three_bridge_intersection_decomposable (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (h : Lower M Γ n) {W X Y Z I A B C : Set α}
    (hW : IsHyperplane M W) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hZ : IsHyperplane M Z) (hI : IsHyperplane M I)
    (hWX : TutteAdjacent M W X) (hXY : TutteAdjacent M X Y)
    (hYZ : TutteAdjacent M Y Z) (hZW : TutteAdjacent M Z W)
    (hWo : W ∉ Γ) (hXo : X ∉ Γ) (hYo : Y ∉ Γ) (hZo : Z ∉ Γ) (hIo : I ∉ Γ)
    (hB : Indecomposable M B) (hC : Indecomposable M C)
    (hBX : B ⊆ X) (hBI : B ⊆ I) (hCZ : C ⊆ Z) (hCI : C ⊆ I)
    (hAW : A ⊆ W) (hAB : A ⊆ B) (hAC : A ⊆ C)
    (hrA : natRank M M.E - natRank M A ≤ n)
    (hrB : natRank M M.E - natRank M (B ∩ Y) ≤ n)
    (hrC : natRank M M.E - natRank M (C ∩ Y) ≤ n)
    (hnot : ¬ NullHomotopic M Γ (TuttePath.square hW hX hY hZ hWX hXY hYZ hZW)) :
    ¬ Indecomposable M (Y ∩ I) := by
  intro hind
  have proper : ∀ F H, F ⊆ H → IsHyperplane M H → F ≠ M.E := by
    intro F H hFH hH heq
    exact hH.2.1 (Set.Subset.antisymm hH.1.subset_ground (heq ▸ hFH))
  obtain ⟨q,hqY,hqI,hqOn,hqo⟩ := path_theorem M hM Γ hΓ (Y ∩ I) hind
    (proper _ _ Set.inter_subset_left hY) Y I hY hI Set.inter_subset_left Set.inter_subset_right hYo hIo
  obtain ⟨p,hpX,hpI,hpOn,hpo⟩ := path_theorem M hM Γ hΓ B hB (proper _ _ hBX hX)
    X I hX hI hBX hBI hXo hIo
  obtain ⟨r,hrZ,hrI,hrOn,hro⟩ := path_theorem M hM Γ hΓ C hC (proper _ _ hCZ hZ)
    Z I hZ hI hCZ hCI hZo hIo
  let a := TuttePath.edge hW hX hWX
  let u := TuttePath.edge hX hY hXY
  let v := TuttePath.edge hY hZ hYZ
  let d := TuttePath.edge hZ hW hZW
  have hn := Lower.null_via_three_bridges hΓ h a u v d p q r rfl rfl rfl rfl
    hqY.symm hrZ.symm hpX.symm (hqI.trans hpI.symm) hqY.symm (hrI.trans hqI.symm)
    (TuttePath.edge_off _ _ _ hWo hXo) (TuttePath.edge_off _ _ _ hXo hYo)
    (TuttePath.edge_off _ _ _ hYo hZo) (TuttePath.edge_off _ _ _ hZo hWo) hpo hqo hro
    (TuttePath.edge_on _ _ _ hAW (hAB.trans hBX))
    (TuttePath.edge_on _ _ _ (hAC.trans hCZ) hAW)
    (fun i => hAB.trans (hpOn i)) (fun i => hAC.trans (hrOn i))
    (TuttePath.edge_on _ _ _ (Set.inter_subset_left.trans hBX) Set.inter_subset_right)
    (fun i => (Set.subset_inter Set.inter_subset_right (Set.inter_subset_left.trans hBI)).trans (hqOn i))
    (fun i => Set.inter_subset_left.trans (hpOn i))
    (TuttePath.edge_on _ _ _ Set.inter_subset_right (Set.inter_subset_left.trans hCZ))
    (fun i => Set.inter_subset_left.trans (hrOn i))
    (fun i => (Set.subset_inter Set.inter_subset_right (Set.inter_subset_left.trans hCI)).trans (hqOn i))
    hrA hrB hrC
  apply hnot
  have heq : TuttePath.square hW hX hY hZ hWX hXY hYZ hZW =
      (a.concat (u.concat v rfl) rfl).concat d rfl := by
    apply TuttePath.ext_vertices (p := TuttePath.square hW hX hY hZ hWX hXY hYZ hZW)
      (q := (a.concat (u.concat v rfl) rfl).concat d rfl) rfl
    intro i; fin_cases i <;> rfl
  rw [heq]
  exact hn
end TutteFormalization.Homotopy
