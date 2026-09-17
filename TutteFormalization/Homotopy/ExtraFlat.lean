import TutteFormalization.Homotopy.CommonSquareBridge

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)
include c

/-- The extra-flat branch of Special, retaining the two auxiliary squares
and the earlier pole obstruction. The non-null assumption is discharged. -/
theorem null_of_extra_flat (hM : Connected M) (hΓ : ModularCut M Γ) (hlower : Lower M Γ 3)
    {Q : Set α} (hQ : Indecomposable M Q) (hrQ : natRank M Q + 3 = natRank M M.E)
    (hDQ : s.D ⊆ Q) (hQL : Q ⊆ s.W ∩ s.Y) (hn₁ : s.F₁ ≠ Q) (hn₂ : s.F₂ ≠ Q) :
    NullHomotopic M Γ s.path := by
  by_contra hnot
  obtain ⟨A,ha,hAW,hnAY⟩ := s.exists_typeA_under_W
  obtain ⟨U,V,hU,hV,hLU,hLV,hUW,hVW,hUV,hiU,hoV,hoU',hiV',all⟩ :=
    c.first_pencil_count hM hΓ hlower hnot ha hAW hnAY
  have hb₁ := (c.pencil_inter_typeB ha hAW hnAY hU hLU hUW).1
  have hb₂ := (c.pencil_inter_typeB ha hAW hnAY hV hLV hVW).1
  have hp₁ := c.pencil_first_pole ha hAW hnAY hU hLU hUW
  have hp₂ := c.pencil_first_pole ha hAW hnAY hV hLV hVW
  have ho₁ : M.closure ((U ∩ c.T) ∪ Q) ∉ Γ :=
    c.extra_pole_off hΓ s.first_indec hQ s.first_rank hrQ s.D_subset_first hDQ
      (fun _ h => ⟨h.1.1,h.2⟩) hQL hn₁ hb₁ (hp₁.symm ▸ hiU)
  have ho₂ : M.closure ((V ∩ c.T) ∪ Q) ∉ Γ :=
    c.extra_pole_off hΓ s.second_indec hQ s.second_rank hrQ s.D_subset_second hDQ
      (fun _ h => ⟨h.2,h.1.1⟩) hQL hn₂ hb₂ hiV'
  let H := M.closure ((U ∩ c.T) ∪ Q)
  have hH : IsHyperplane M H :=
    transversal_two_join_hyperplane hQ hrQ s.middle_corank s.middle_decomp hQL
      s.hW s.hY s.W_ne_Y Set.inter_subset_left Set.inter_subset_right hb₁.1.1
      hb₁.2.1 hDQ hb₁.2.2.1 hb₁.2.2.2.1 hb₁.2.2.2.2
  have hQH : Q ⊆ H := M.subset_closure_of_subset' Set.subset_union_right hQ.1.subset_ground
  have hBH : U ∩ c.T ⊆ H := M.subset_closure_of_subset' Set.subset_union_left hb₁.1.1.subset_ground
  have hWH : s.W ≠ H := fun he => hb₁.2.2.2.1 (hBH.trans_eq he.symm)
  have hYH : s.Y ≠ H := fun he => hb₁.2.2.2.2 (hBH.trans_eq he.symm)
  have null₁ := s.withSecond_null hQ hrQ hQL hH ho₁ hQH hWH hYH
    hM hΓ hlower c.rankD hDQ hn₁ hb₂ (hp₂.symm ▸ hoV) ho₂
  have null₂ := s.flip.withSecond_null hQ hrQ hQL hH ho₁ hQH hWH hYH
    hM hΓ hlower (by simpa only [SpecialData.flip_D] using c.rankD)
    (by simpa only [SpecialData.flip_D] using hDQ)
    (by simpa only [SpecialData.flip_first] using hn₂)
    ((s.flip_typeB _).mpr hb₁)
    (by simpa only [SpecialData.flip_first] using hoU') ho₁
  have edges := third_hyperplane_adjacent hQ hrQ s.middle_corank s.middle_decomp hQL
    s.hW s.hY s.W_ne_Y Set.inter_subset_left Set.inter_subset_right hH hWH hYH hQH
  exact hnot (square_null_of_two_auxiliary hΓ s.hW s.hX s.hY s.hZ hH
    s.hWX s.hXY s.hYZ s.hZW edges.2.symm edges.1 null₁ null₂)
end TutteFormalization.Homotopy.CountingFrame

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Extra-flat conclusion without assuming a counting frame: under temporary
non-nullness, the frame is constructed from the proved earlier dependencies. -/
theorem null_of_extra_flat (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hrD : natRank M s.D + 4 = natRank M M.E)
    {Q : Set α} (hQ : Indecomposable M Q) (hrQ : natRank M Q + 3 = natRank M M.E)
    (hDQ : s.D ⊆ Q) (hQL : Q ⊆ s.W ∩ s.Y) (hn₁ : s.F₁ ≠ Q) (hn₂ : s.F₂ ≠ Q) :
    NullHomotopic M Γ s.path := by
  by_contra hn
  obtain ⟨c⟩ := s.exists_countingFrame hM hΓ hlower hrD hn
  exact hn (c.null_of_extra_flat hM hΓ hlower hQ hrQ hDQ hQL hn₁ hn₂)
end TutteFormalization.Homotopy.SpecialData
