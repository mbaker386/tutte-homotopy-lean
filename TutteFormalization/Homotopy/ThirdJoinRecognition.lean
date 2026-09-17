import TutteFormalization.Homotopy.ThirdRecognition
import TutteFormalization.Homotopy.TripleJoinSpanning

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Actual third-kind recognition for the joins in source 2.2.2. This local
recognition does not remove the requirement to retain the manuscript's later
residual-case split in the main proof (semantic contract S4). -/
theorem third_elementary_from_joins (hΓ : ModularCut M Γ) {F G L P H K J U V Z : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hU : IsHyperplane M U) (hV : IsHyperplane M V) (hZ : IsHyperplane M Z)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hJV : TutteAdjacent M J V) (hVH : TutteAdjacent M V H)
    (hF : F = H ∩ K ∩ J) (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hFL : F ⊆ L) (hLH : L ⊆ H) (hGL : G ⊆ L) (hGK : ¬ G ⊆ K)
    (hP : CorankTwo M P) (hFP : F ⊆ P) (hPJ : P ⊆ J) (hPQ : P ≠ K ∩ J) (hPH : ¬ P ⊆ H)
    (hu : M.closure ((H ∩ K) ∪ P) = U) (hv : M.closure (L ∪ P) = V)
    (hz : M.closure (L ∪ (K ∩ J)) = Z) (hUH : U ≠ H) (hUK : U ≠ K) (hVZ : V ≠ Z)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ) (hoV : V ∉ Γ)
    (hUΓ : U ∈ Γ) (hZΓ : Z ∈ Γ) :
    Elementary M Γ (TuttePath.square hH hK hJ hV hHK hKJ hJV hVH) := by
  let pts : Fin 4 → Set α := ![H ∩ K,L,K ∩ J,P]
  have hFflat : M.IsFlat F := hF.symm ▸ flat_inter (flat_inter hH.1 hK.1) hJ.1
  have hFA : F ⊆ H ∩ K := hF ▸ Set.inter_subset_left
  have hFQ : F ⊆ K ∩ J := by rw [hF]; exact fun _ hx => ⟨hx.1.2,hx.2⟩
  have hrA := corankTwo_natRank hHK.2.2
  have hrL := corankTwo_natRank hL
  have hrQ := corankTwo_natRank hKJ.2.2
  have hrP := corankTwo_natRank hP
  have h01 : H ∩ K ≠ L := fun he => hGK (hGL.trans (he.symm ▸ Set.inter_subset_right))
  have h02 : H ∩ K ≠ K ∩ J := by
    intro he
    have hAJ : H ∩ K ⊆ J := he ▸ Set.inter_subset_right
    have hh : H ∩ K = F := by rw [hF,Set.inter_eq_left.mpr hAJ]
    rw [hh] at hrA
    omega
  have h03 : H ∩ K ≠ P := fun he => hPH (he ▸ Set.inter_subset_left)
  have h12 : L ≠ K ∩ J := fun he => hGK (hGL.trans (he ▸ Set.inter_subset_left))
  have h13 : L ≠ P := fun he => hPH (he ▸ hLH)
  have h23 : K ∩ J ≠ P := hPQ.symm
  have hp : ∀ i, M.IsFlat (pts i) := by
    intro i; fin_cases i
    · exact hHK.2.2.1
    · exact hL.1
    · exact hKJ.2.2.1
    · exact hP.1
  have hfp : ∀ i, F ⊆ pts i := by intro i; fin_cases i <;> assumption
  have hrp : ∀ i, natRank M (pts i) = natRank M F + 1 := by
    intro i; fin_cases i <;> dsimp [pts] <;> omega
  have hinj : Function.Injective pts := by
    intro i j he
    fin_cases i <;> fin_cases j <;> dsimp [pts] at he
    all_goals first
      | rfl
      | exact False.elim (h01 he)
      | exact False.elim (h01 he.symm)
      | exact False.elim (h02 he)
      | exact False.elim (h02 he.symm)
      | exact False.elim (h03 he)
      | exact False.elim (h03 he.symm)
      | exact False.elim (h12 he)
      | exact False.elim (h12 he.symm)
      | exact False.elim (h13 he)
      | exact False.elim (h13 he.symm)
      | exact False.elim (h23 he)
      | exact False.elim (h23 he.symm)
  have hrH := hyperplane_natRank hH
  have hrK := hyperplane_natRank hK
  have hrJ := hyperplane_natRank hJ
  have j01 : M.closure (pts 0 ∪ pts 1) = H := cover_flats_join_eq (F := F) hH.1
    (hp 0) (hp 1) Set.inter_subset_left hLH (hrp 0) (hrp 1) (by omega) h01
  have j02 : M.closure (pts 0 ∪ pts 2) = K := cover_flats_join_eq (F := F) hK.1
    (hp 0) (hp 2) Set.inter_subset_right Set.inter_subset_left (hrp 0) (hrp 2) (by omega) h02
  have j23 : M.closure (pts 2 ∪ pts 3) = J := cover_flats_join_eq (F := F) hJ.1
    (hp 2) (hp 3) Set.inter_subset_right hPJ (hrp 2) (hrp 3) (by omega) h23
  have hs := four_triples_span pts
    (triple_spans_of_pair_joins (hp 0) (hp 1) (hp 2) hH hK hHK.1 j01 j02)
    (triple_spans_of_pair_joins (hp 0) (hp 1) (hp 3) hH hU hUH.symm j01 hu)
    (triple_spans_of_pair_joins (hp 0) (hp 2) (hp 3) hK hU hUK.symm j02 hu)
    (triple_spans_of_pair_joins (hp 1) (hp 2) (hp 3) hZ hV hVZ.symm hz hv)
  exact third_elementary_of_four_covers hΓ hFflat hrF pts hp hfp hrp hinj hs
    j01 j02 j23 hv (hz.symm ▸ hZΓ) (hu.symm ▸ hUΓ)
    hH hK hJ hV hHK hKJ hJV hVH hoH hoK hoJ hoV
end TutteFormalization.Homotopy
