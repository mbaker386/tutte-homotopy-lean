import TutteFormalization.Homotopy.LargeCorankStep

namespace TutteFormalization.Homotopy.LargeBridge
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s : LargeCorankStep M Γ D G} (b : LargeBridge M Γ s)

theorem P_not_H : ¬ b.P ⊆ s.H := by
  intro hh
  apply b.aboveP.2
  exact fun _ hx => ⟨⟨hh hx,(b.belowP hx).1⟩,(b.belowP hx).2⟩

theorem D_subset_P : D ⊆ b.P := s.D_subset_F.trans b.aboveP.1

theorem P_subset_middle : b.P ⊆ b.T ∩ s.B := Set.subset_inter b.PT (b.belowP.trans Set.inter_subset_left)

/-- Case 2.3, decomposable L': construct the actual special square and
prove its distinct triple flats and carrier bound before applying Special. -/
theorem exists_special_insertion (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ}
    (hlower : Lower M Γ n) (hG : Indecomposable M G) (hDG : D ⊆ G)
    (hrG : natRank M G = natRank M D + 1) (hrD : natRank M M.E - natRank M D ≤ n+1)
    (hnR : ¬ Indecomposable M (b.T ∩ s.B)) :
    ∃ U, ∃ hU : IsHyperplane M U, ∃ hTU : TutteAdjacent M b.T U,
      ∃ hUB : TutteAdjacent M U s.B,
        U ∉ Γ ∧ G ⊆ U ∧ b.P ⊆ U ∧
        NullHomotopic M Γ (TuttePath.square b.hT hU s.hB s.hH hTU hUB s.hHB.symm b.hHT) := by
  obtain ⟨K',hK',hPK',hKR,hrK'⟩ := exists_indecomposable_corankThree b.hP b.corankTB hnR b.P_subset_middle
  have hDK' : D ⊆ K' := b.D_subset_P.trans hPK'
  have hGR : ¬ G ⊆ b.T ∩ s.B := fun hh => s.badB (hh.trans Set.inter_subset_right)
  obtain ⟨hiS,hcS⟩ := transversal_cover_join hK' hrK' b.corankTB hnR hKR.1
    hG.1 hDG hDK' hrG hGR
  let S := M.closure (G ∪ K')
  have hST : S ⊆ b.T := (M.closure_mono (Set.union_subset b.goodT (hKR.1.trans Set.inter_subset_left))).trans_eq b.hT.1.closure
  have hGS : G ⊆ S := M.subset_closure_of_subset' Set.subset_union_left hG.1.subset_ground
  have hKS : K' ⊆ S := M.subset_closure_of_subset' Set.subset_union_right hK'.1.subset_ground
  obtain ⟨U,hU,hSU,hUT,hoU⟩ := exists_other_off_hyperplane hΓ hiS hcS b.hT hST b.offT
  have hGU : G ⊆ U := hGS.trans hSU
  have hUB : U ≠ s.B := fun he => s.badB (hGU.trans_eq he)
  have hadj := third_hyperplane_adjacent hK' hrK' b.corankTB hnR hKR.1
    b.hT s.hB b.neB Set.inter_subset_left Set.inter_subset_right hU hUT.symm hUB.symm (hKS.trans hSU)
  have hTU := hadj.1.symm
  have hrS := corankTwo_natRank hcS
  have hSB := (hyperplane_inter_of_cover hK'.1 hcS.1 s.hB hKS (hKR.1.trans Set.inter_subset_right)
    (by omega) (fun hh => s.badB (hGS.trans hh))).1
  have hTUmeet := hyperplane_inter_eq_of_corankTwo hcS b.hT hU hUT.symm hST hSU
  have hfirst : b.T ∩ U ∩ s.B = K' := by rw [hTUmeet,hSB]
  have hsecond : s.B ∩ s.H ∩ b.T = b.K := by rw [Set.inter_comm s.B s.H]; exact b.triple
  let sq : SpecialData M Γ := {
    W := b.T, X := U, Y := s.B, Z := s.H
    hW := b.hT, hX := hU, hY := s.hB, hZ := s.hH
    hWX := hTU, hXY := hadj.2, hYZ := s.hHB.symm, hZW := b.hHT
    offW := b.offT, offX := hoU, offY := s.offB, offZ := s.offH
    first_indec := hfirst.symm ▸ hK'
    second_indec := hsecond.symm ▸ b.hK
    first_rank := hfirst.symm ▸ hrK'
    second_rank := hsecond.symm ▸ b.rankK
    middle_corank := b.corankTB, middle_decomp := hnR }
  have hneq : sq.F₁ ≠ sq.F₂ := by
    change b.T ∩ U ∩ s.B ≠ s.B ∩ s.H ∩ b.T
    rw [hfirst,hsecond]
    intro he
    exact b.P_not_H ((hPK'.trans_eq he).trans (b.belowK.trans Set.inter_subset_left))
  have hDU : D ⊆ U := hDG.trans hGU
  have hDsq : D ⊆ sq.D := fun _ hx => ⟨⟨⟨b.PT (b.D_subset_P hx),hDU hx⟩,s.onB hx⟩,s.onH hx⟩
  have hbound : natRank M M.E - natRank M sq.D ≤ n+1 := by
    have hm := natRank_mono (M := M) hDsq
    omega
  exact ⟨U,hU,hTU,hadj.2,hoU,hGU,hPK'.trans (hKS.trans hSU),
    sq.null_of_carrier_bound hM hΓ hlower hneq hbound⟩
end TutteFormalization.Homotopy.LargeBridge
