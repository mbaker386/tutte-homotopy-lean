import TutteFormalization.Homotopy.ResidualTransport

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G}

/-- The extra flat in the residual branch, after failure of the historical
all-flats containment condition. All fields are concrete geometric facts. -/
structure ExtraCover (c : SelectedCover s) where
  I : Set α
  indec : Indecomposable M I
  corank : CorankTwo M I
  above : s.F ⊆ I
  not_U : ¬ I ⊆ c.U
  not_Z : ¬ I ⊆ s.Z

namespace ExtraCover
variable {c : SelectedCover s} (e : ExtraCover c)
def W₁ : Set α := M.closure (s.L ∪ e.I)
def W₂ : Set α := M.closure ((s.K ∩ s.J) ∪ e.I)
def W₃ : Set α := M.closure ((s.H ∩ s.K) ∪ e.I)

theorem I_subset_W₁ : e.I ⊆ e.W₁ := M.subset_closure_of_subset' Set.subset_union_right e.indec.1.subset_ground

theorem I_subset_W₂ : e.I ⊆ e.W₂ := M.subset_closure_of_subset' Set.subset_union_right e.indec.1.subset_ground

theorem I_subset_W₃ : e.I ⊆ e.W₃ := M.subset_closure_of_subset' Set.subset_union_right e.indec.1.subset_ground

theorem L_subset_W₁ : s.L ⊆ e.W₁ := M.subset_closure_of_subset' Set.subset_union_left (M.isFlat_closure _).subset_ground

theorem Q_subset_W₂ : s.K ∩ s.J ⊆ e.W₂ := M.subset_closure_of_subset' Set.subset_union_left s.hKJ.2.2.1.subset_ground

theorem A_subset_W₃ : s.H ∩ s.K ⊆ e.W₃ := M.subset_closure_of_subset' Set.subset_union_left s.hHK.2.2.1.subset_ground

theorem not_both_first_middle : ¬ (e.I ⊆ s.H ∧ e.I ⊆ s.K) := by
  rintro ⟨hH,hK⟩
  have hrI := corankTwo_natRank e.corank
  have hrA := corankTwo_natRank s.hHK.2.2
  have he := flat_eq_of_subset_of_natRank_le e.indec.1 s.hHK.2.2.1 (Set.subset_inter hH hK) (by omega)
  exact e.not_U (he ▸ c.A_subset_U)

theorem W₁_properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) :
    IsHyperplane M e.W₁ ∧ e.W₁ ≠ s.Z ∧ e.W₁ ∉ Γ ∧ G ⊆ e.W₁ := by
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hz := s.Z_properties hΓ hD hG hDG hrG
  obtain ⟨hw,hn,ho⟩ := extra_join_off hΓ s.F_indec.1 s.triple_rank hl.1 e.corank s.F_subset_L e.above
    hz.1 (M.subset_closure_of_subset' Set.subset_union_left hl.1.1.subset_ground) hZΓ e.not_Z s.hH hl.2.1 s.offH
  exact ⟨hw,hn,ho,(s.G_subset_L hG.1).trans e.L_subset_W₁⟩

theorem W₂_properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) :
    IsHyperplane M e.W₂ ∧ e.W₂ ≠ s.Z ∧ e.W₂ ∉ Γ ∧ ¬ G ⊆ e.W₂ := by
  have hz := s.Z_properties hΓ hD hG hDG hrG
  have hFQ : s.F ⊆ s.K ∩ s.J := fun _ hx => ⟨hx.1.2,hx.2⟩
  obtain ⟨hw,hn,ho⟩ := extra_join_off hΓ s.F_indec.1 s.triple_rank s.hKJ.2.2 e.corank hFQ e.above
    hz.1 (M.subset_closure_of_subset' Set.subset_union_right s.hKJ.2.2.1.subset_ground) hZΓ e.not_Z
    s.hK Set.inter_subset_left s.offK
  refine ⟨hw,hn,ho,?_⟩
  intro hGW
  have hLW : s.L ⊆ e.W₂ := (M.closure_mono (Set.union_subset hGW (e.above.trans e.I_subset_W₂))).trans_eq hw.1.closure
  have hZW : s.Z ⊆ e.W₂ := (M.closure_mono (Set.union_subset hLW e.Q_subset_W₂)).trans_eq hw.1.closure
  have hrZ := hyperplane_natRank hz.1
  have hrW := hyperplane_natRank hw
  exact hn (flat_eq_of_subset_of_natRank_le hz.1.1 hw.1 hZW (by omega)).symm

theorem W₃_properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ) :
    IsHyperplane M e.W₃ ∧ e.W₃ ≠ c.U ∧ e.W₃ ∉ Γ := by
  have hU := (c.properties hΓ hD hG hDG hrG hZΓ).1
  exact extra_join_off hΓ s.F_indec.1 s.triple_rank s.hHK.2.2 e.corank Set.inter_subset_left e.above
    hU c.A_subset_U hUΓ e.not_U s.hK Set.inter_subset_right s.offK

theorem P_join_off (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ) :
    IsHyperplane M (M.closure (e.I ∪ c.P)) ∧ M.closure (e.I ∪ c.P) ∉ Γ := by
  have hU := (c.properties hΓ hD hG hDG hrG hZΓ).1
  have hh := extra_join_off hΓ s.F_indec.1 s.triple_rank c.corank e.corank c.above e.above
    hU c.P_subset_U hUΓ e.not_U s.hJ c.below s.offJ
  simpa only [Set.union_comm] using And.intro hh.1 hh.2.2
end ExtraCover
end TutteFormalization.Homotopy
