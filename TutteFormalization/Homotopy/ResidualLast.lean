import TutteFormalization.Homotopy.SelectedThird

namespace TutteFormalization.Homotopy.SelectedCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} (c : SelectedCover s)

/-- Source residual Case 2.2.2.1. An extra indecomposable flat below the
successor replaces P; its new U is off by cut uniqueness above H∩K. -/
theorem reduced_of_extra_below_last (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    {I : Set α} (hI : Indecomposable M I) (hcI : CorankTwo M I) (hFI : s.F ⊆ I)
    (hIJ : I ⊆ s.J) (hnIU : ¬ I ⊆ c.U) (hnIZ : ¬ I ⊆ s.Z) : s.Reduced := by
  by_cases hIH : I ⊆ s.H
  · exact s.reduced_of_cover_below hΓ hI hcI hIH hIJ
  have hIQ : I ≠ s.K ∩ s.J := by
    intro he
    have hQZ : s.K ∩ s.J ⊆ s.Z := M.subset_closure_of_subset' Set.subset_union_right s.hKJ.2.2.1.subset_ground
    exact hnIZ (he ▸ hQZ)
  let d : SelectedCover s := ⟨I,hI,hcI,hFI,hIJ,hIQ,hIH⟩
  have hU := (c.properties hΓ hD hG hDG hrG hZΓ).1
  have hU' := (d.properties hΓ hD hG hDG hrG hZΓ).1
  have ho : d.U ∉ Γ := by
    intro hm
    have he := cut_hyperplanes_unique_above hΓ s.hHK.2.2 s.hK Set.inter_subset_right s.offK
      hU' hU d.A_subset_U c.A_subset_U hm hUΓ
    exact hnIU (d.P_subset_U.trans_eq he)
  exact d.reduced_of_U_off hΓ hD hG hDG hrG hZΓ ho
end TutteFormalization.Homotopy.SelectedCover
