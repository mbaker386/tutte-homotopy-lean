import TutteFormalization.Homotopy.SelectedCover

namespace TutteFormalization.Homotopy.SelectedCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} (c : SelectedCover s)

/-- Actual third-kind recognition in the selected configuration. -/
theorem third_elementary (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ) :
    ∃ hV : IsHyperplane M c.V, ∃ hVJ : TutteAdjacent M c.V s.J, ∃ hVH : TutteAdjacent M c.V s.H,
      Elementary M Γ (TuttePath.square s.hH s.hK s.hJ hV s.hHK s.hKJ hVJ.symm hVH) := by
  obtain ⟨hU,hV,hUH,hUK,_,_,_,_,hVZ,_,hoV⟩ := c.properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨_,_,_,_,_,hVJ,hVH⟩ := c.edges hΓ hD hG hDG hrG hZΓ
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hz := s.Z_properties hΓ hD hG hDG hrG
  refine ⟨hV,hVJ,hVH,?_⟩
  exact third_elementary_from_joins hΓ s.hH s.hK s.hJ hU hV hz.1 s.hHK s.hKJ hVJ.symm hVH
    rfl s.triple_rank hl.1 s.F_subset_L hl.2.1 (s.G_subset_L hG.1) s.badK
    c.corank c.above c.below c.not_edge c.not_first rfl rfl rfl hUH hUK hVZ
    s.offH s.offK s.offJ hoV hUΓ hZΓ

/-- The manuscript's all-flats-contained branch. S4's local third-kind
recognition proves the move; the historical premise is retained here so the
main proof still splits off and checks each of its four residual cases. -/
theorem reduced_of_all_contained (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    (_hall : ∀ I, Indecomposable M I → CorankTwo M I → s.F ⊆ I → I ⊆ c.U ∨ I ⊆ s.Z) :
    s.Reduced := by
  obtain ⟨hV,hVJ,hVH,he⟩ := c.third_elementary hΓ hD hG hDG hrG hZΓ hUΓ
  have hn := elementary_null he
  have hh := square_shortcut hΓ s.hH s.hK s.hJ hV s.hHK s.hKJ hVJ.symm hVH hn
  have hGV := (s.G_subset_L hG.1).trans c.L_subset_V
  exact ⟨(TuttePath.edge s.hH hV hVH.symm).concat (TuttePath.edge hV s.hJ hVJ) rfl,hh,
    TuttePath.concat_on (TuttePath.edge_on _ _ _ s.onH (hDG.trans hGV))
      (TuttePath.edge_on _ _ _ (hDG.trans hGV) s.onJ) rfl,
    twoEdge_count_decreases s.hH s.hK s.hJ hV s.hHK s.hKJ hVH.symm hVJ hGV s.badK⟩
end TutteFormalization.Homotopy.SelectedCover
