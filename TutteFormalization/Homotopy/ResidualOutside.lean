import TutteFormalization.Homotopy.FiveTriangleExchange

namespace TutteFormalization.Homotopy.ExtraCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} {c : SelectedCover s} (e : ExtraCover c)

/-- Source residual Case 2.2.2.4 with all five elementary triangles, actual
replacement vertices, unchanged local count and the final off-U° reduction. -/
theorem reduced_of_outside (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    (hnIH : ¬ e.I ⊆ s.H) (hnIK : ¬ e.I ⊆ s.K) (hnIJ : ¬ e.I ⊆ s.J) : s.Reduced := by
  obtain ⟨h1,_,ho1,hG1⟩ := e.W₁_properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨h2,_,ho2,hG2⟩ := e.W₂_properties hΓ hD hG hDG hrG hZΓ
  obtain ⟨h3,_,ho3⟩ := e.W₃_properties hΓ hD hG hDG hrG hZΓ hUΓ
  obtain ⟨n12,n13,n23,n1H,n2K,n2J,n3H,n3K⟩ :=
    e.outside_distinct hΓ hD hG hDG hrG hZΓ hUΓ hnIH hnIK hnIJ
  have hH3 := tutteAdjacent_of_corankTwo s.hHK.2.1 s.hHK.2.2 s.hH h3 n3H.symm Set.inter_subset_left e.A_subset_W₃
  have h3K := tutteAdjacent_of_corankTwo s.hHK.2.1 s.hHK.2.2 h3 s.hK n3K e.A_subset_W₃ Set.inter_subset_right
  have hK2 := tutteAdjacent_of_corankTwo s.hKJ.2.1 s.hKJ.2.2 s.hK h2 n2K.symm Set.inter_subset_left e.Q_subset_W₂
  have h2J := tutteAdjacent_of_corankTwo s.hKJ.2.1 s.hKJ.2.2 h2 s.hJ n2J e.Q_subset_W₂ Set.inter_subset_right
  have h32 := tutteAdjacent_of_corankTwo e.indec e.corank h3 h2 n23.symm e.I_subset_W₃ e.I_subset_W₂
  have h31 := tutteAdjacent_of_corankTwo e.indec e.corank h3 h1 n13.symm e.I_subset_W₃ e.I_subset_W₁
  have h12 := tutteAdjacent_of_corankTwo e.indec e.corank h1 h2 n12 e.I_subset_W₁ e.I_subset_W₂
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hiL := (c.edges hΓ hD hG hDG hrG hZΓ).1
  have hH1 := tutteAdjacent_of_corankTwo hiL hl.1 s.hH h1 n1H.symm hl.2.1 e.L_subset_W₁
  have m32 := hyperplane_inter_eq_of_corankTwo e.corank h3 h2 n23.symm e.I_subset_W₃ e.I_subset_W₂
  have m31 := hyperplane_inter_eq_of_corankTwo e.corank h3 h1 n13.symm e.I_subset_W₃ e.I_subset_W₁
  have m12 := hyperplane_inter_eq_of_corankTwo e.corank h1 h2 n12 e.I_subset_W₁ e.I_subset_W₂
  have m2J := hyperplane_inter_eq_of_corankTwo s.hKJ.2.2 h2 s.hJ n2J e.Q_subset_W₂ Set.inter_subset_right
  have hrI := corankTwo_natRank e.corank
  have hrF : natRank M s.F + 3 = natRank M M.E := s.triple_rank
  have hFH : s.F ⊆ s.H := fun _ hx => hx.1.1
  have hFK : s.F ⊆ s.K := fun _ hx => hx.1.2
  have hFJ : s.F ⊆ s.J := Set.inter_subset_right
  have mIH := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hH e.above hFH (by omega) hnIH).1
  have mIK := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hK e.above hFK (by omega) hnIK).1
  have mIJ := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hJ e.above hFJ (by omega) hnIJ).1
  have ht3 : e.W₃ ∩ s.K ∩ e.W₂ = s.F := by
    calc
      e.W₃ ∩ s.K ∩ e.W₂ = s.K ∩ (e.W₃ ∩ e.W₂) := by ext x; simp only [Set.mem_inter_iff]; tauto
      _ = s.F := by rw [m32,Set.inter_comm s.K e.I,mIK]
  have ht5 : s.H ∩ e.W₃ ∩ e.W₁ = s.F := by rw [Set.inter_assoc,m31,Set.inter_comm s.H e.I,mIH]
  have n1 := elementary_null (triangle_rankTwo_elementary hΓ s.hHK.2.2 s.hH h3 s.hK hH3 h3K s.hHK.symm
    Set.inter_subset_left e.A_subset_W₃ Set.inter_subset_right s.offH ho3 s.offK)
  have n2 := elementary_null (triangle_rankTwo_elementary hΓ s.hKJ.2.2 s.hK h2 s.hJ hK2 h2J s.hKJ.symm
    Set.inter_subset_left e.Q_subset_W₂ Set.inter_subset_right s.offK ho2 s.offJ)
  have n3 := elementary_null (triangle_rankThree_elementary hΓ h3 s.hK h2 h3K hK2 h32.symm
    (ht3.symm ▸ s.triple_rank) ho3 s.offK ho2)
  have n4 := elementary_null (triangle_rankTwo_elementary hΓ e.corank h3 h1 h2 h31 h12 h32.symm
    e.I_subset_W₃ e.I_subset_W₁ e.I_subset_W₂ ho3 ho1 ho2)
  have n5 := elementary_null (triangle_rankThree_elementary hΓ s.hH h3 h1 hH3 h31 hH1.symm
    (ht5.symm ▸ s.triple_rank) s.offH ho3 ho1)
  have htF : e.W₁ ∩ e.W₂ ∩ s.J = s.F := by rw [m12,mIJ]
  have hD2 : D ⊆ e.W₂ := s.D_subset_F.trans (e.above.trans e.I_subset_W₂)
  let t : CorankThreeStep M Γ D G := {
    H := e.W₁, K := e.W₂, J := s.J
    hH := h1, hK := h2, hJ := s.hJ
    hHK := h12, hKJ := h2J
    offH := ho1, offK := ho2, offJ := s.offJ
    onH := hDG.trans hG1, onK := hD2, onJ := s.onJ
    goodH := hG1, badK := hG2
    triple_rank := htF.symm ▸ s.triple_rank }
  have htf : t.F = s.F := htF
  have htz : t.Z = s.Z := by
    change M.closure (M.closure (G ∪ t.F) ∪ (e.W₂ ∩ s.J)) = _
    rw [htf,m2J]; rfl
  have hnewU : M.closure ((t.H ∩ t.K) ∪ c.P) ∉ Γ := by
    change M.closure ((e.W₁ ∩ e.W₂) ∪ c.P) ∉ Γ
    rw [m12]
    exact (e.P_join_off hΓ hD hG hDG hrG hZΓ hUΓ).2
  have hPQ : c.P ≠ t.K ∩ t.J := by change c.P ≠ e.W₂ ∩ s.J; rw [m2J]; exact c.not_edge
  have htred := t.reduced_of_candidate_off hΓ hD hG hDG hrG (htz.symm ▸ hZΓ)
    c.indec c.corank (htf.symm ▸ c.above) c.below hPQ hnewU
  let a := TuttePath.edge s.hH h1 hH1
  have hh : Homotopic M Γ s.path (a.concat t.path rfl) :=
    five_triangle_exchange hΓ s.hH s.hK s.hJ h1 h2 h3 s.hHK s.hKJ hH3 h3K hK2 h2J h32 h31 h12 hH1 n1 n2 n3 n4 n5
  have hc : outsideCount t.path G ≤ outsideCount s.path G := by
    classical
    rw [outsideCount_word,outsideCount_word]
    change [e.W₁,e.W₂,s.J].countP _ ≤ [s.H,s.K,s.J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [hG1,hG2,s.goodH,s.badK]
  exact CorankThreeStep.reduced_of_good_prefix a
    (TuttePath.edge_on _ _ _ s.onH (hDG.trans hG1)) (TuttePath.edge_on _ _ _ s.goodH hG1)
    ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ s.offH ho1)) rfl hh hc htred
end TutteFormalization.Homotopy.ExtraCover
