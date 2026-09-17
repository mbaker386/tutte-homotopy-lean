import TutteFormalization.Homotopy.CountingFrame
import TutteFormalization.Homotopy.SpecialFlatAvoidance

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- There is at most one cut hyperplane above a corank-two flat below an off one. -/
theorem cut_hyperplanes_unique_above (hΓ : ModularCut M Γ) {L Q H K : Set α}
    (hL : CorankTwo M L) (hQ : IsHyperplane M Q) (hLQ : L ⊆ Q) (hQo : Q ∉ Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hLH : L ⊆ H) (hLK : L ⊆ K)
    (hHΓ : H ∈ Γ) (hKΓ : K ∈ Γ) : H = K := by
  by_contra hne
  have hi := hyperplane_inter_eq_of_corankTwo hL hH hK hne hLH hLK
  have hLΓ : L ∈ Γ := hi ▸ hΓ.hyperplane_inter_mem hH hK hne (by simpa only [hi] using hL) hHΓ hKΓ
  exact hQo (hΓ.upward L Q hLΓ hQ.1 hLQ)

/-- B.26's lower bound uses only the unprimed pencil over L₁ (HD-009). -/
theorem exists_two_other_hyperplanes {L Q : Set α} (hL : Indecomposable M L)
    (hc : CorankTwo M L) : ∃ H K, IsHyperplane M H ∧ IsHyperplane M K ∧
      L ⊆ H ∧ L ⊆ K ∧ H ≠ Q ∧ K ≠ Q ∧ H ≠ K := by
  obtain ⟨H,K,R,hH,hK,hR,hHK,hHR,hKR,hLH,hLK,hLR⟩ :=
    (corankTwo_indecomposable_iff_three hc).mp hL
  by_cases hHQ : H = Q
  · subst H
    exact ⟨K,R,hK,hR,hLK,hLR,hHK.symm,hHR.symm,hKR⟩
  by_cases hKQ : K = Q
  · subst K
    exact ⟨H,R,hH,hR,hLH,hLR,hHK,hKR.symm,hHR⟩
  exact ⟨H,K,hH,hK,hLH,hLK,hHQ,hKQ,hHK⟩

namespace CountingFrame
variable {s : SpecialData M Γ} (c : CountingFrame s)

theorem first_not_below_T : ¬ s.F₁ ⊆ c.T :=
  special_flat_not_below_hyperplane s.first_indec s.first_rank s.hW s.hY c.hT
    s.middle_corank s.middle_decomp (fun _ h => ⟨h.1.1,h.2⟩)
    c.decompWT c.decompYT c.corankYT

theorem second_not_below_T : ¬ s.F₂ ⊆ c.T :=
  special_flat_not_below_hyperplane s.second_indec s.second_rank s.hW s.hY c.hT
    s.middle_corank s.middle_decomp (fun _ h => ⟨h.2,h.1.1⟩)
    c.decompWT c.decompYT c.corankYT

include c in
/-- The source's Diamond choice inside each unprimed hyperplane. -/
theorem exists_typeB_in_pencil {A H : Set α} (ha : s.TypeA A)
    (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y)
    (hH : IsHyperplane M H) (hAH : A ⊆ H) (hHW : H ≠ s.W) :
    ∃ B, s.TypeB B ∧ A ⊆ B ∧ B ⊆ H := by
  have hrH := hyperplane_natRank hH
  have hrA := ha.2.2.1
  have hrD := c.rankD
  obtain ⟨B,C,hB,hC,hAB,hAC,hBH,hCH,hBC,hBr,hCr⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hH) ha.1 hAH (by omega)
  have hj := cover_flats_join_eq hH.1 hB.1 hC.1 hBH hCH hBr hCr (by omega) hBC
  by_cases hBW : B ⊆ s.W
  · have hnCW : ¬ C ⊆ s.W := by
      intro hCW
      have hHW' : H ⊆ s.W := hj ▸
        (M.closure_mono (Set.union_subset hBW hCW)).trans_eq s.hW.1.closure
      exact hyperplane_not_subset hH s.hW hHW hHW'
    exact ⟨C,⟨hC,ha.2.1.trans hAC,by omega,hnCW,fun h => hnAY (hAC.trans h)⟩,hAC,hCH⟩
  · exact ⟨B,⟨hB,ha.2.1.trans hAB,by omega,hBW,fun h => hnAY (hAB.trans h)⟩,hAB,hBH⟩
end CountingFrame
end TutteFormalization.Homotopy
