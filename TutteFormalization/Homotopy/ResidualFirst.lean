import TutteFormalization.Homotopy.ResidualMiddle

namespace TutteFormalization.Homotopy.ExtraCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} {c : SelectedCover s} (e : ExtraCover c)

/-- Source residual Case 2.2.2.3: replace K by the bad W2 using the two
specified triangles, then reduce via the off join I∨P. -/
theorem reduced_of_below_first (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    (hIH : e.I ⊆ s.H) (hnIJ : ¬ e.I ⊆ s.J) : s.Reduced := by
  obtain ⟨hW,hWZ,hoW,hGW⟩ := e.W₂_properties hΓ hD hG hDG hrG hZΓ
  have hIK : ¬ e.I ⊆ s.K := fun hh => e.not_both_first_middle ⟨hIH,hh⟩
  have hWK : e.W₂ ≠ s.K := fun he => hIK (e.I_subset_W₂.trans_eq he)
  have hWJ : e.W₂ ≠ s.J := fun he => hnIJ (e.I_subset_W₂.trans_eq he)
  have hrQ := corankTwo_natRank s.hKJ.2.2
  have hrI := corankTwo_natRank e.corank
  have hrF : natRank M s.F + 3 = natRank M M.E := s.triple_rank
  have hWH : e.W₂ ≠ s.H := by
    intro he
    have hQH : s.K ∩ s.J ⊆ s.H := e.Q_subset_W₂.trans_eq he
    have hQF : s.K ∩ s.J = s.F := Set.Subset.antisymm
      (fun _ hx => ⟨⟨hQH hx,hx.1⟩,hx.2⟩) (fun _ hx => ⟨hx.1.2,hx.2⟩)
    rw [hQF] at hrQ
    omega
  have hHWedge := tutteAdjacent_of_corankTwo e.indec e.corank s.hH hW hWH.symm hIH e.I_subset_W₂
  have hWJedge := tutteAdjacent_of_corankTwo s.hKJ.2.1 s.hKJ.2.2 hW s.hJ hWJ e.Q_subset_W₂ Set.inter_subset_right
  have hKWedge := tutteAdjacent_of_corankTwo s.hKJ.2.1 s.hKJ.2.2 s.hK hW hWK.symm Set.inter_subset_left e.Q_subset_W₂
  have hHWmeet := hyperplane_inter_eq_of_corankTwo e.corank s.hH hW hWH.symm hIH e.I_subset_W₂
  have hWJmeet := hyperplane_inter_eq_of_corankTwo s.hKJ.2.2 hW s.hJ hWJ e.Q_subset_W₂ Set.inter_subset_right
  have hKWmeet := hyperplane_inter_eq_of_corankTwo s.hKJ.2.2 s.hK hW hWK.symm Set.inter_subset_left e.Q_subset_W₂
  have hFJ : s.F ⊆ s.J := Set.inter_subset_right
  have hIJmeet := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hJ e.above hFJ (by omega) hnIJ).1
  have htF : s.H ∩ e.W₂ ∩ s.J = s.F := by rw [hHWmeet,hIJmeet]
  have htriangle : s.H ∩ s.K ∩ e.W₂ = s.F := by
    rw [Set.inter_assoc,hKWmeet,← Set.inter_assoc]; rfl
  have hDW : D ⊆ e.W₂ := s.D_subset_F.trans (e.above.trans e.I_subset_W₂)
  let t : CorankThreeStep M Γ D G := {
    H := s.H, K := e.W₂, J := s.J
    hH := s.hH, hK := hW, hJ := s.hJ
    hHK := hHWedge, hKJ := hWJedge
    offH := s.offH, offK := hoW, offJ := s.offJ
    onH := s.onH, onK := hDW, onJ := s.onJ
    goodH := s.goodH, badK := hGW
    triple_rank := htF.symm ▸ s.triple_rank }
  have htf : t.F = s.F := htF
  have htz : t.Z = s.Z := by
    change M.closure (M.closure (G ∪ t.F) ∪ (e.W₂ ∩ s.J)) = _
    rw [htf,hWJmeet]; rfl
  have hnewU : M.closure ((t.H ∩ t.K) ∪ c.P) ∉ Γ := by
    change M.closure ((s.H ∩ e.W₂) ∪ c.P) ∉ Γ
    rw [hHWmeet]
    exact (e.P_join_off hΓ hD hG hDG hrG hZΓ hUΓ).2
  have hPQ : c.P ≠ t.K ∩ t.J := by change c.P ≠ e.W₂ ∩ s.J; rw [hWJmeet]; exact c.not_edge
  have htred := t.reduced_of_candidate_off hΓ hD hG hDG hrG (htz.symm ▸ hZΓ)
    c.indec c.corank (htf.symm ▸ c.above) c.below hPQ hnewU
  have tri1 := triangle_shortcut hΓ s.hH s.hK hW s.hHK hKWedge hHWedge.symm
    (elementary_null (triangle_rankThree_elementary hΓ s.hH s.hK hW s.hHK hKWedge hHWedge.symm
      (htriangle.symm ▸ s.triple_rank) s.offH s.offK hoW))
  have tri2 := triangle_shortcut hΓ s.hK hW s.hJ hKWedge hWJedge s.hKJ.symm
    (elementary_null (triangle_rankTwo_elementary hΓ s.hKJ.2.2 s.hK hW s.hJ hKWedge hWJedge s.hKJ.symm
      Set.inter_subset_left e.Q_subset_W₂ Set.inter_subset_right s.offK hoW s.offJ))
  have hh : Homotopic M Γ s.path t.path := triangle_exchange s.hH s.hK s.hJ hW
    s.hHK s.hKJ hHWedge hKWedge hWJedge tri1 tri2
  have hc : outsideCount t.path G ≤ outsideCount s.path G := by
    classical
    rw [outsideCount_word,outsideCount_word]
    change [s.H,e.W₂,s.J].countP _ ≤ [s.H,s.K,s.J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [hGW,s.badK]
  exact CorankThreeStep.reduced_of_homotopic hh hc htred
end TutteFormalization.Homotopy.ExtraCover
