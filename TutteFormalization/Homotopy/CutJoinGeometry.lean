import TutteFormalization.Homotopy.NextCoverChoice

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.2's U and V, with all distinctness used by its triangle and
third-kind constructions. These facts precede the split on U's cut membership. -/
theorem cut_join_geometry (hΓ : ModularCut M Γ) {F G L P H K J Z : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hF : F = H ∩ K ∩ J) (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hFL : F ⊆ L) (hLH : L ⊆ H)
    (hGL : G ⊆ L) (hGK : ¬ G ⊆ K)
    (hP : CorankTwo M P) (hFP : F ⊆ P) (hPJ : P ⊆ J)
    (hPQ : P ≠ K ∩ J) (hPH : ¬ P ⊆ H)
    (hZ : IsHyperplane M Z) (hLZ : L ⊆ Z) (hQZ : K ∩ J ⊆ Z)
    (hz : Z = M.closure (L ∪ (K ∩ J))) (hZΓ : Z ∈ Γ) (hoH : H ∉ Γ) (hoJ : J ∉ Γ) :
    let U := M.closure ((H ∩ K) ∪ P)
    let V := M.closure (L ∪ P)
    IsHyperplane M U ∧ IsHyperplane M V ∧ U ≠ H ∧ U ≠ K ∧ U ≠ J ∧
      V ≠ H ∧ V ≠ K ∧ V ≠ J ∧ V ≠ Z ∧ U ≠ V ∧ V ∉ Γ := by
  dsimp only
  let U := M.closure ((H ∩ K) ∪ P)
  let V := M.closure (L ∪ P)
  have hFflat : M.IsFlat F := hF.symm ▸ flat_inter (flat_inter hH.1 hK.1) hJ.1
  have hFA : F ⊆ H ∩ K := hF ▸ Set.inter_subset_left
  have hrA := corankTwo_natRank hHK.2.2
  have hrP := corankTwo_natRank hP
  have hrL := corankTwo_natRank hL
  have hrQ := corankTwo_natRank hKJ.2.2
  have neAP : H ∩ K ≠ P := fun he => hPH (he ▸ Set.inter_subset_left)
  have neLP : L ≠ P := fun he => hPH (he ▸ hLH)
  have hU : IsHyperplane M U := corankTwo_join_isHyperplane hFflat hrF hHK.2.2 hP hFA hFP neAP
  have hV : IsHyperplane M V := corankTwo_join_isHyperplane hFflat hrF hL hP hFL hFP neLP
  have hAU : H ∩ K ⊆ U := M.subset_closure_of_subset' Set.subset_union_left hHK.2.2.1.subset_ground
  have hPU : P ⊆ U := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have hLV : L ⊆ V := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hPV : P ⊆ V := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have eqhyp {A B : Set α} (ha : IsHyperplane M A) (hb : IsHyperplane M B) (hs : A ⊆ B) : A = B := by
    have hra := hyperplane_natRank ha
    have hrb := hyperplane_natRank hb
    exact flat_eq_of_subset_of_natRank_le ha.1 hb.1 hs (by omega)
  have hPK : ¬ P ⊆ K := fun hh => hPQ
    (flat_eq_of_subset_of_natRank_le hP.1 hKJ.2.2.1 (Set.subset_inter hh hPJ) (by omega))
  have hAJ : ¬ H ∩ K ⊆ J := by
    intro hh
    have he : H ∩ K = F := by rw [hF,Set.inter_eq_left.mpr hh]
    rw [he] at hrA
    omega
  have hUH : U ≠ H := fun he => hPH (hPU.trans_eq he)
  have hUK : U ≠ K := fun he => hPK (hPU.trans_eq he)
  have hUJ : U ≠ J := fun he => hAJ (hAU.trans_eq he)
  have hVH : V ≠ H := fun he => hPH (hPV.trans_eq he)
  have hVK : V ≠ K := fun he => hGK ((hGL.trans hLV).trans_eq he)
  have hZJ : Z ≠ J := fun he => hoJ (he ▸ hZΓ)
  have hVJ : V ≠ J := by
    intro he
    have hZsub : Z ⊆ J := by
      rw [hz]
      exact (M.closure_mono (Set.union_subset (hLV.trans_eq he) Set.inter_subset_right)).trans_eq hJ.1.closure
    exact hZJ (eqhyp hZ hJ hZsub)
  have hJZ : J ∩ Z = K ∩ J := hyperplane_inter_eq_of_corankTwo hKJ.2.2 hJ hZ hZJ.symm
    Set.inter_subset_right hQZ
  have hVZ : V ≠ Z := by
    intro he
    have hPQsub : P ⊆ K ∩ J := (Set.subset_inter hPJ (hPV.trans_eq he)).trans_eq hJZ
    exact hPQ (flat_eq_of_subset_of_natRank_le hP.1 hKJ.2.2.1 hPQsub (by omega))
  have hLA : L ≠ H ∩ K := fun he => hGK (hGL.trans (he ▸ Set.inter_subset_right))
  have hHr := hyperplane_natRank hH
  have hLAjoin : M.closure (L ∪ (H ∩ K)) = H := cover_flats_join_eq (F := F) hH.1 hL.1 hHK.2.2.1
    hLH Set.inter_subset_left (by omega) (by omega) (by omega) hLA
  have hUV : U ≠ V := by
    intro he
    have hHU : H ⊆ U := by
      rw [← hLAjoin]
      exact (M.closure_mono (Set.union_subset (hLV.trans_eq he.symm) hAU)).trans_eq hU.1.closure
    exact hUH (eqhyp hH hU hHU).symm
  refine ⟨hU,hV,hUH,hUK,hUJ,hVH,hVK,hVJ,hVZ,hUV,?_⟩
  intro hm
  exact hVZ (cut_hyperplanes_unique_above hΓ hL hH hLH hoH hV hZ hLV hLZ hm hZΓ)
end TutteFormalization.Homotopy
