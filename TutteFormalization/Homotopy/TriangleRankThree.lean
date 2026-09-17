import TutteFormalization.Homotopy.RankThreePointModel
import TutteFormalization.Homotopy.TrianglePaths

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {H K L : Set α}

/-- Second-kind recognition for a triangle whose triple intersection has
corank three: the three edge intersections form the actual Boolean model. -/
theorem triangle_rankThree_elementary (hΓ : ModularCut M Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L) (hLH : TutteAdjacent M L H)
    (hrD : natRank M (H ∩ K ∩ L) + 3 = natRank M M.E)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoL : L ∉ Γ) :
    Elementary M Γ (TuttePath.triangle hH hK hL hHK hKL hLH) := by
  let D := H ∩ K ∩ L
  let P : Fin 3 → Set α := ![H ∩ K,H ∩ L,K ∩ L]
  have hD : M.IsFlat D := flat_inter (flat_inter hH.1 hK.1) hL.1
  have hc0 := hHK.2.2
  have hc1 : CorankTwo M (H ∩ L) := by simpa only [Set.inter_comm] using hLH.2.2
  have hc2 := hKL.2.2
  have hr0 := corankTwo_natRank hc0
  have hr1 := corankTwo_natRank hc1
  have hr2 := corankTwo_natRank hc2
  have hn0L : ¬ H ∩ K ⊆ L := by
    intro hh
    have hm := natRank_mono (M := M) (show H ∩ K ⊆ D from fun _ hx => ⟨hx,hh hx⟩)
    change natRank M (H ∩ K) ≤ natRank M (H ∩ K ∩ L) at hm
    omega
  have hn1K : ¬ H ∩ L ⊆ K := by
    intro hh
    have hm := natRank_mono (M := M) (show H ∩ L ⊆ D from fun _ hx => ⟨⟨hx.1,hh hx⟩,hx.2⟩)
    change natRank M (H ∩ L) ≤ natRank M (H ∩ K ∩ L) at hm
    omega
  have hn2H : ¬ K ∩ L ⊆ H := by
    intro hh
    have hm := natRank_mono (M := M) (show K ∩ L ⊆ D from fun _ hx => ⟨⟨hh hx,hx.1⟩,hx.2⟩)
    change natRank M (K ∩ L) ≤ natRank M (H ∩ K ∩ L) at hm
    omega
  have h01 : H ∩ K ≠ H ∩ L := fun he => hn0L (he ▸ Set.inter_subset_right)
  have h02 : H ∩ K ≠ K ∩ L := fun he => hn0L (he ▸ Set.inter_subset_right)
  have h12 : H ∩ L ≠ K ∩ L := fun he => hn1K (he ▸ Set.inter_subset_left)
  have hp : ∀ i, M.IsFlat (P i) := by intro i; fin_cases i; exact hc0.1; exact hc1.1; exact hc2.1
  have hd : ∀ i, D ⊆ P i := by
    intro i; fin_cases i
    · exact Set.inter_subset_left
    · exact fun _ hx => ⟨hx.1.1,hx.2⟩
    · exact fun _ hx => ⟨hx.1.2,hx.2⟩
  have hr : ∀ i, natRank M (P i) = natRank M D + 1 := by
    intro i; fin_cases i <;> change _ = natRank M (H ∩ K ∩ L) + 1 <;> dsimp [P] <;> omega
  have hi : Function.Injective P := by
    intro i j he
    fin_cases i <;> fin_cases j <;> dsimp [P] at he
    all_goals first
      | rfl
      | exact False.elim (h01 he)
      | exact False.elim (h01 he.symm)
      | exact False.elim (h02 he)
      | exact False.elim (h02 he.symm)
      | exact False.elim (h12 he)
      | exact False.elim (h12 he.symm)
  have hrH := hyperplane_natRank hH
  have hrK := hyperplane_natRank hK
  have hrL := hyperplane_natRank hL
  have j01 : M.closure (P 0 ∪ P 1) = H := cover_flats_join_eq hH.1 (hp 0) (hp 1)
    Set.inter_subset_left Set.inter_subset_left (hr 0) (hr 1) (by change _ = natRank M (H ∩ K ∩ L) + 2; omega) h01
  have j02 : M.closure (P 0 ∪ P 2) = K := cover_flats_join_eq hK.1 (hp 0) (hp 2)
    Set.inter_subset_right Set.inter_subset_left (hr 0) (hr 2) (by change _ = natRank M (H ∩ K ∩ L) + 2; omega) h02
  have j12 : M.closure (P 1 ∪ P 2) = L := cover_flats_join_eq hL.1 (hp 1) (hp 2)
    Set.inter_subset_right Set.inter_subset_right (hr 1) (hr 2) (by change _ = natRank M (H ∩ K ∩ L) + 2; omega) h12
  have hs : M.closure ((P 0 ∪ P 1) ∪ P 2) = M.E := by
    have hHJ : H ⊆ M.closure ((P 0 ∪ P 1) ∪ P 2) := j01 ▸ M.closure_mono Set.subset_union_left
    rcases hH.2.2 _ (M.isFlat_closure _) hHJ with he | he
    · exact False.elim (hn2H ((M.subset_closure_of_subset' Set.subset_union_right hc2.1.subset_ground).trans_eq he))
    · exact he
  obtain ⟨φ,hbottom,hφ⟩ := exists_rankThreePointEmbedding hD hrD P hp hd hr hi hs
  have pair_image (i j : Fin 3) : φ.image {i,j} = M.closure (P i ∪ P j) := by
    have hc : u33.closure ({i} ∪ {j}) = {i,j} := by
      have hcl : ∀ i j : Fin 3, u33.closure ({i} ∪ {j}) = {i,j} := by decide
      exact hcl i j
    simpa only [hc,hφ] using φ.map_join {i} {j} (u33_simple.2 i).1 (u33_simple.2 j).1
  have im01 : φ.image {0,1} = H := (pair_image 0 1).trans j01
  have im02 : φ.image {0,2} = K := (pair_image 0 2).trans j02
  have im12 : φ.image {1,2} = L := (pair_image 1 2).trans j12
  let C : Fin 3 → Finset (Fin 3) := ![{0,1},{0,2},{1,2}]
  have hc : ∀ i, u33.Flat (C i) := by decide
  have ho : ∀ i, φ.image (C i) ∉ cutPlus M Γ := by
    intro i; fin_cases i
    · change φ.image {0,1} ∉ _; rw [im01]; exact (hyperplane_off_cutPlus hH).mpr hoH
    · change φ.image {0,2} ∉ _; rw [im02]; exact (hyperplane_off_cutPlus hK).mpr hoK
    · change φ.image {1,2} ∉ _; rw [im12]; exact (hyperplane_off_cutPlus hL).mpr hoL
  have cover : ∀ F, u33.Flat F → F ≠ Finset.univ → ∃ i, F ⊆ C i := by decide
  have hcut := exactTopCut_of_cover φ hΓ C hc ho cover
  refine Elementary.base (BaseElementary.secondB φ _ hcut ?_ ?_ rfl
    ((off_cutPlus _).mpr (TuttePath.triangle_off hH hK hL hHK hKL hLH hoH hoK hoL)))
  · intro i; rw [hφ]; fin_cases i
    · exact hHK.2.1
    · change Indecomposable M (H ∩ L)
      simpa only [Set.inter_comm] using hLH.2.1
    · exact hKL.2.1
  · rw [TuttePath.triangle_word]
    simp only [List.map_cons,List.map_nil,im01,im02,im12]
end TutteFormalization.Homotopy
