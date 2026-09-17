import TutteFormalization.Homotopy.ResidualFirst

namespace TutteFormalization.Homotopy.ExtraCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} {c : SelectedCover s} (e : ExtraCover c)

/-- The distinctness of W1,W2,W3 in residual 2.2.2.4, including all
endpoint distinctions needed by the five triangles. -/
theorem outside_distinct (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    (hnIH : ¬ e.I ⊆ s.H) (hnIK : ¬ e.I ⊆ s.K) (hnIJ : ¬ e.I ⊆ s.J) :
    e.W₁ ≠ e.W₂ ∧ e.W₁ ≠ e.W₃ ∧ e.W₂ ≠ e.W₃ ∧
      e.W₁ ≠ s.H ∧ e.W₂ ≠ s.K ∧ e.W₂ ≠ s.J ∧ e.W₃ ≠ s.H ∧ e.W₃ ≠ s.K := by
  obtain ⟨hW1,_,_,hGW1⟩ := e.W₁_properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨hW2,_,_,hGW2⟩ := e.W₂_properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨hW3,_,_⟩ := e.W₃_properties hΓ hD hG hDG hrG hZΓ hUΓ
  have h12 : e.W₁ ≠ e.W₂ := fun he => hGW2 (hGW1.trans_eq he)
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hrL := corankTwo_natRank hl.1
  have hrA := corankTwo_natRank s.hHK.2.2
  have hrQ := corankTwo_natRank s.hKJ.2.2
  have hrF : natRank M s.F + 3 = natRank M M.E := s.triple_rank
  have hrH := hyperplane_natRank s.hH
  have hrK := hyperplane_natRank s.hK
  have hLA : s.L ≠ s.H ∩ s.K := fun he => s.badK ((s.G_subset_L hG.1).trans (he ▸ Set.inter_subset_right))
  have hLAjoin : M.closure (s.L ∪ (s.H ∩ s.K)) = s.H := cover_flats_join_eq (F := s.F)
    s.hH.1 hl.1.1 s.hHK.2.2.1 hl.2.1 Set.inter_subset_left (by omega) (by omega) (by omega) hLA
  have hAQ : s.H ∩ s.K ≠ s.K ∩ s.J := by
    intro he
    have hh : s.F = s.H ∩ s.K := Set.inter_eq_left.mpr (he ▸ Set.inter_subset_right)
    rw [hh] at hrF
    omega
  have hAQjoin : M.closure ((s.H ∩ s.K) ∪ (s.K ∩ s.J)) = s.K := cover_flats_join_eq (F := s.F)
    s.hK.1 s.hHK.2.2.1 s.hKJ.2.2.1 Set.inter_subset_right Set.inter_subset_left (by omega) (by omega) (by omega) hAQ
  have h13 : e.W₁ ≠ e.W₃ := by
    intro he
    have hs : s.H ⊆ e.W₃ := by
      rw [← hLAjoin]
      exact (M.closure_mono (Set.union_subset (e.L_subset_W₁.trans_eq he) e.A_subset_W₃)).trans_eq hW3.1.closure
    have hrW := hyperplane_natRank hW3
    have heH := flat_eq_of_subset_of_natRank_le s.hH.1 hW3.1 hs (by omega)
    exact hnIH (e.I_subset_W₃.trans_eq heH.symm)
  have h23 : e.W₂ ≠ e.W₃ := by
    intro he
    have hs : s.K ⊆ e.W₃ := by
      rw [← hAQjoin]
      exact (M.closure_mono (Set.union_subset e.A_subset_W₃ (e.Q_subset_W₂.trans_eq he))).trans_eq hW3.1.closure
    have hrW := hyperplane_natRank hW3
    have heK := flat_eq_of_subset_of_natRank_le s.hK.1 hW3.1 hs (by omega)
    exact hnIK (e.I_subset_W₃.trans_eq heK.symm)
  exact ⟨h12,h13,h23,(fun he => hnIH (e.I_subset_W₁.trans_eq he)),
    (fun he => hnIK (e.I_subset_W₂.trans_eq he)),(fun he => hnIJ (e.I_subset_W₂.trans_eq he)),
    (fun he => hnIH (e.I_subset_W₃.trans_eq he)),(fun he => hnIK (e.I_subset_W₃.trans_eq he))⟩
end TutteFormalization.Homotopy.ExtraCover
