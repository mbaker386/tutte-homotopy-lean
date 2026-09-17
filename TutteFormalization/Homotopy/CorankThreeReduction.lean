import TutteFormalization.Homotopy.ResidualOutside

namespace TutteFormalization.Homotopy.CorankThreeStep
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}

/-- Complete source Case 2.2, retaining the all-flats condition and all four
historical residual cases. Every branch returns an actual local decrease. -/
theorem reduced (s : CorankThreeStep M Γ D G) (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hrD : natRank M M.E - natRank M D ≤ n+1) : s.Reduced := by
  classical
  by_cases hz : s.Z ∈ Γ
  swap
  · exact s.reduced_of_Z_off hM hΓ hlower hD hG hDG hrG hrD hz
  obtain ⟨P,hP,hcP,hFP,hPJ,hPQ⟩ := exists_other_corankTwo (Q := s.K ∩ s.J)
    s.F_indec s.triple_rank s.hJ (show s.F ⊆ s.J from Set.inter_subset_right)
  by_cases hPH : P ⊆ s.H
  · exact s.reduced_of_cover_below hΓ hP hcP hPH hPJ
  let c : SelectedCover s := ⟨P,hP,hcP,hFP,hPJ,hPQ,hPH⟩
  by_cases hu : c.U ∈ Γ
  swap
  · exact c.reduced_of_U_off hΓ hD hG hDG hrG hz hu
  by_cases hall : ∀ I, Indecomposable M I → CorankTwo M I → s.F ⊆ I → I ⊆ c.U ∨ I ⊆ s.Z
  · exact c.reduced_of_all_contained hΓ hD hG hDG hrG hz hu hall
  push_neg at hall
  obtain ⟨I,hI,hcI,hFI,hnIU,hnIZ⟩ := hall
  let e : ExtraCover c := ⟨I,hI,hcI,hFI,hnIU,hnIZ⟩
  by_cases hIJ : I ⊆ s.J
  · exact c.reduced_of_extra_below_last hΓ hD hG hDG hrG hz hu hI hcI hFI hIJ hnIU hnIZ
  by_cases hIK : I ⊆ s.K
  · exact e.reduced_of_below_middle hΓ hD hG hDG hrG hz hu hIK hIJ
  by_cases hIH : I ⊆ s.H
  · exact e.reduced_of_below_first hΓ hD hG hDG hrG hz hu hIH hIJ
  · exact e.reduced_of_outside hΓ hD hG hDG hrG hz hu hIH hIK hIJ
end TutteFormalization.Homotopy.CorankThreeStep
