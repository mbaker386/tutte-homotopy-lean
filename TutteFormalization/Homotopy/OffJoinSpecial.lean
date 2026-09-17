import TutteFormalization.Homotopy.DecomposableBridge
import TutteFormalization.Homotopy.SpecialBound

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.1's auxiliary special path, including the distinct triple flats
and the bound needed for the nonrecursive Special/Lower application. -/
theorem exists_off_special_bridge (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) {D F G L H K Z : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hZ : IsHyperplane M Z)
    (hHK : TutteAdjacent M H K) (hKZ : TutteAdjacent M K Z)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoZ : Z ∉ Γ)
    (hF : Indecomposable M F) (hFeq : H ∩ K ∩ Z = F)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hG : Indecomposable M G) (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L)
    (hLmeet : H ∩ Z = L) (hHZ : H ≠ Z) (hGL : G ⊆ L) (hGK : ¬ G ⊆ K)
    (hDG : D ⊆ G) (hDF : D ⊆ F) (hrD : natRank M M.E - natRank M D ≤ n+1) :
    ∃ T, ∃ hT : IsHyperplane M T, ∃ hTH : TutteAdjacent M T H,
      ∃ hTZ : TutteAdjacent M T Z,
        T ∉ Γ ∧ G ⊆ T ∧
        NullHomotopic M Γ (TuttePath.square hH hK hZ hT hHK hKZ hTZ.symm hTH) := by
  have hLH : L ⊆ H := hLmeet ▸ Set.inter_subset_left
  have hLZ : L ⊆ Z := hLmeet ▸ Set.inter_subset_right
  obtain ⟨P,T,hP,hrP,hGP,hPL,hT,hoT,hGT,hTH,hTZ,hPeq⟩ :=
    exists_decomposable_bridge hΓ hG hL hnL hGL hH hZ hHZ hLH hLZ hoH
  let s : SpecialData M Γ := {
    W := H, X := K, Y := Z, Z := T
    hW := hH, hX := hK, hY := hZ, hZ := hT
    hWX := hHK, hXY := hKZ, hYZ := hTZ.symm, hZW := hTH
    offW := hoH, offX := hoK, offY := hoZ, offZ := hoT
    first_indec := hFeq.symm ▸ hF
    second_indec := hPeq.symm ▸ hP
    first_rank := hFeq.symm ▸ hrF
    second_rank := hPeq.symm ▸ hrP
    middle_corank := hLmeet.symm ▸ hL
    middle_decomp := hLmeet.symm ▸ hnL }
  have hneq : s.F₁ ≠ s.F₂ := by
    change H ∩ K ∩ Z ≠ Z ∩ T ∩ H
    rw [hFeq,hPeq]
    intro he
    have hFK : F ⊆ K := hFeq ▸ (fun _ hx => hx.1.2)
    exact hGK ((hGP.trans_eq he.symm).trans hFK)
  have hsub : D ⊆ s.D := by
    intro x hx
    have hf : x ∈ H ∩ K ∩ Z := hFeq.symm ▸ hDF hx
    exact ⟨hf,hGT (hDG hx)⟩
  have hr : natRank M M.E - natRank M s.D ≤ n+1 := by
    have hm := natRank_mono (M := M) hsub
    omega
  exact ⟨T,hT,hTH,hTZ,hoT,hGT,s.null_of_carrier_bound hM hΓ hlower hneq hr⟩
end TutteFormalization.Homotopy
