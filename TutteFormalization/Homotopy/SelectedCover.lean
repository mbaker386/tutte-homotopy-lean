import TutteFormalization.Homotopy.CorankThreeStep

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}

/-- The actual Diamond-selected flat in the noncontained branch of 2.2.2. -/
structure SelectedCover (s : CorankThreeStep M Γ D G) where
  P : Set α
  indec : Indecomposable M P
  corank : CorankTwo M P
  above : s.F ⊆ P
  below : P ⊆ s.J
  not_edge : P ≠ s.K ∩ s.J
  not_first : ¬ P ⊆ s.H

namespace SelectedCover
variable {s : CorankThreeStep M Γ D G} (c : SelectedCover s)
def U : Set α := M.closure ((s.H ∩ s.K) ∪ c.P)
def V : Set α := M.closure (s.L ∪ c.P)

theorem A_subset_U : s.H ∩ s.K ⊆ c.U := M.subset_closure_of_subset' Set.subset_union_left s.hHK.2.2.1.subset_ground

theorem P_subset_U : c.P ⊆ c.U := M.subset_closure_of_subset' Set.subset_union_right c.indec.1.subset_ground

theorem P_subset_V : c.P ⊆ c.V := M.subset_closure_of_subset' Set.subset_union_right c.indec.1.subset_ground

theorem L_subset_V : s.L ⊆ c.V := M.subset_closure_of_subset' Set.subset_union_left (M.isFlat_closure _).subset_ground

theorem properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) :
    IsHyperplane M c.U ∧ IsHyperplane M c.V ∧ c.U ≠ s.H ∧ c.U ≠ s.K ∧ c.U ≠ s.J ∧
      c.V ≠ s.H ∧ c.V ≠ s.K ∧ c.V ≠ s.J ∧ c.V ≠ s.Z ∧ c.U ≠ c.V ∧ c.V ∉ Γ := by
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hz := s.Z_properties hΓ hD hG hDG hrG
  exact cut_join_geometry hΓ s.hH s.hK s.hJ s.hHK s.hKJ rfl s.triple_rank hl.1
    s.F_subset_L hl.2.1 (s.G_subset_L hG.1) s.badK c.corank c.above c.below c.not_edge c.not_first
    hz.1 (M.subset_closure_of_subset' Set.subset_union_left hl.1.1.subset_ground)
    (M.subset_closure_of_subset' Set.subset_union_right s.hKJ.2.2.1.subset_ground) rfl hZΓ s.offH s.offJ

theorem edges (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) :
    Indecomposable M s.L ∧ TutteAdjacent M s.H c.U ∧ TutteAdjacent M s.K c.U ∧
      TutteAdjacent M c.U s.J ∧ TutteAdjacent M c.U c.V ∧ TutteAdjacent M c.V s.J ∧
      TutteAdjacent M c.V s.H := by
  obtain ⟨hU,hV,hUH,hUK,hUJ,hVH,_,hVJ,hVZ,hUV,_⟩ := c.properties hΓ hD hG hDG hrG hZΓ
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hz := s.Z_properties hΓ hD hG hDG hrG
  exact cut_branch_edges s.hHK.2.1 s.hHK.2.2 Set.inter_subset_left Set.inter_subset_right c.A_subset_U
    hl.1 hl.2.1 (M.subset_closure_of_subset' Set.subset_union_left hl.1.1.subset_ground) c.L_subset_V
    c.indec c.corank c.below c.P_subset_U c.P_subset_V s.hH s.hK s.hJ hz.1 hU hV
    hz.2.1 hVH hVZ hUH hUK hUJ hUV hVJ

theorem reduced_of_U_off (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ)
    (hoU : c.U ∉ Γ) : s.Reduced := by
  obtain ⟨hU,hV,_,_,_,_,_,_,_,_,hoV⟩ := c.properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨_,hHU,hKU,hUJ,hUV,hVJ,hVH⟩ := c.edges hΓ hD hG hDG hrG hZΓ
  have hGV := (s.G_subset_L hG.1).trans c.L_subset_V
  exact four_triangle_shortcut hΓ s.hH s.hK s.hJ hU hV s.hHK s.hKJ hHU hKU hUJ hUV hVJ hVH
    rfl s.triple_rank c.A_subset_U c.corank c.above c.P_subset_U c.P_subset_V c.below c.not_first
    s.offH s.offK s.offJ hoU hoV s.onH s.onJ (hDG.trans hGV) hGV s.badK
end SelectedCover
end TutteFormalization.Homotopy
