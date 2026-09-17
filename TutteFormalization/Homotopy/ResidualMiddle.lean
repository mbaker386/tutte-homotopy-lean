import TutteFormalization.Homotopy.ExtraCover

namespace TutteFormalization.Homotopy.ExtraCover
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : CorankThreeStep M Γ D G} {c : SelectedCover s} (e : ExtraCover c)

/-- Source residual Case 2.2.2.2. Insert the good W1 before K, retaining K;
the new U°=I∨P is off, so the checked easy case reduces the new segment. -/
theorem reduced_of_below_middle (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ) (hUΓ : c.U ∈ Γ)
    (hIK : e.I ⊆ s.K) (hnIJ : ¬ e.I ⊆ s.J) : s.Reduced := by
  obtain ⟨hW,hWZ,hoW,hGW⟩ := e.W₁_properties hΓ hD hG hDG hrG hZΓ
  have hIH : ¬ e.I ⊆ s.H := fun hh => e.not_both_first_middle ⟨hh,hIK⟩
  have hWH : e.W₁ ≠ s.H := fun he => hIH (e.I_subset_W₁.trans_eq he)
  have hWK : e.W₁ ≠ s.K := fun he => s.badK (hGW.trans_eq he)
  have hWKedge := tutteAdjacent_of_corankTwo e.indec e.corank hW s.hK hWK e.I_subset_W₁ hIK
  have hWKmeet := hyperplane_inter_eq_of_corankTwo e.corank hW s.hK hWK e.I_subset_W₁ hIK
  have hl := s.L_properties hΓ hD hG hDG hrG
  have hiL := (c.edges hΓ hD hG hDG hrG hZΓ).1
  have hHWedge := tutteAdjacent_of_corankTwo hiL hl.1 s.hH hW hWH.symm hl.2.1 e.L_subset_W₁
  have hrI := corankTwo_natRank e.corank
  have hrF : natRank M s.F + 3 = natRank M M.E := s.triple_rank
  have hFH : s.F ⊆ s.H := fun _ hx => hx.1.1
  have hFJ : s.F ⊆ s.J := Set.inter_subset_right
  have hIHmeet := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hH e.above hFH (by omega) hIH).1
  have hIJmeet := (hyperplane_inter_of_cover s.F_indec.1 e.indec.1 s.hJ e.above hFJ (by omega) hnIJ).1
  have htF : e.W₁ ∩ s.K ∩ s.J = s.F := by rw [hWKmeet,hIJmeet]
  have htriangle : s.H ∩ e.W₁ ∩ s.K = s.F := by
    rw [Set.inter_assoc,hWKmeet,Set.inter_comm s.H e.I,hIHmeet]
  let t : CorankThreeStep M Γ D G := {
    H := e.W₁, K := s.K, J := s.J
    hH := hW, hK := s.hK, hJ := s.hJ
    hHK := hWKedge, hKJ := s.hKJ
    offH := hoW, offK := s.offK, offJ := s.offJ
    onH := hDG.trans hGW, onK := s.onK, onJ := s.onJ
    goodH := hGW, badK := s.badK
    triple_rank := htF.symm ▸ s.triple_rank }
  have htf : t.F = s.F := htF
  have htz : t.Z = s.Z := by change M.closure (M.closure (G ∪ t.F) ∪ (s.K ∩ s.J)) = _; rw [htf]; rfl
  have hnewU : M.closure ((t.H ∩ t.K) ∪ c.P) ∉ Γ := by
    change M.closure ((e.W₁ ∩ s.K) ∪ c.P) ∉ Γ
    rw [hWKmeet]
    exact (e.P_join_off hΓ hD hG hDG hrG hZΓ hUΓ).2
  have htred := t.reduced_of_candidate_off hΓ hD hG hDG hrG (htz.symm ▸ hZΓ)
    c.indec c.corank (htf.symm ▸ c.above) c.below c.not_edge hnewU
  have tri := triangle_shortcut hΓ s.hH hW s.hK hHWedge hWKedge s.hHK.symm
    (elementary_null (triangle_rankThree_elementary hΓ s.hH hW s.hK hHWedge hWKedge s.hHK.symm
      (htriangle.symm ▸ s.triple_rank) s.offH hoW s.offK))
  let a := TuttePath.edge s.hH hW hHWedge
  have hh : Homotopic M Γ s.path (a.concat t.path rfl) := by
    have h := tri.symm.append (TuttePath.edge s.hK s.hJ s.hKJ)
      ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ s.offK s.offJ)) rfl
    have ha := TuttePath.concat_assoc a (TuttePath.edge hW s.hK hWKedge)
      (TuttePath.edge s.hK s.hJ s.hKJ) rfl rfl
    exact ha ▸ h
  have hc : outsideCount t.path G ≤ outsideCount s.path G := by
    classical
    rw [outsideCount_word,outsideCount_word]
    change [e.W₁,s.K,s.J].countP _ ≤ [s.H,s.K,s.J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [hGW,s.goodH]
  exact CorankThreeStep.reduced_of_good_prefix a
    (TuttePath.edge_on _ _ _ s.onH (hDG.trans hGW)) (TuttePath.edge_on _ _ _ s.goodH hGW)
    ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ s.offH hoW)) rfl hh hc htred
end TutteFormalization.Homotopy.ExtraCover
