import TutteFormalization.Homotopy.TransversalIntersections

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.24: each cover of D lies in two of three pairwise covering hyperplanes. -/
theorem cover_below_pair_plane {D P W Y T : Set α}
    (hD : M.IsFlat D) (hP : M.IsFlat P) (hDP : D ⊆ P)
    (hrP : natRank M P = natRank M D + 1)
    (hW : M.IsFlat W) (hY : M.IsFlat Y) (hT : M.IsFlat T)
    (hDW : D ⊆ W) (hDY : D ⊆ Y) (hDT : D ⊆ T)
    (hWY : W ∪ Y = M.E) (hWT : W ∪ T = M.E) (hYT : Y ∪ T = M.E) :
    P ⊆ W ∩ Y ∨ P ⊆ W ∩ T ∨ P ⊆ Y ∩ T := by
  have hy := flat_cover_under_one_side hD hP hDP hrP hW hY hDW hDY hWY
  have ht := flat_cover_under_one_side hD hP hDP hrP hW hT hDW hDT hWT
  have hyt := flat_cover_under_one_side hD hP hDP hrP hY hT hDY hDT hYT
  rcases hy with hPW | hPY
  · rcases hyt with hPY | hPT
    · exact Or.inl (Set.subset_inter hPW hPY)
    · exact Or.inr (Or.inl (Set.subset_inter hPW hPT))
  · rcases ht with hPW | hPT
    · exact Or.inl (Set.subset_inter hPW hPY)
    · exact Or.inr (Or.inr (Set.subset_inter hPY hPT))

/-- B.25's join calculation in one of the three pair planes. -/
theorem corankTwo_below_one_of_pair {P L W Y : Set α}
    (hP : M.IsFlat P) (hrP : natRank M P + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hPL : P ⊆ L) (hPm : P ⊆ W ∩ Y)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y)
    (hc : CorankTwo M (W ∩ Y)) (hd : ¬ Indecomposable M (W ∩ Y)) :
    L ⊆ W ∨ L ⊆ Y := by
  by_cases heq : W ∩ Y = L
  · exact Or.inl (heq ▸ Set.inter_subset_left)
  have hJ := corankTwo_join_isHyperplane hP hrP hc hL hPm hPL heq
  have hmJ : W ∩ Y ⊆ M.closure ((W ∩ Y) ∪ L) :=
    M.subset_closure_of_subset' Set.subset_union_left hc.1.subset_ground
  have hLJ : L ⊆ M.closure ((W ∩ Y) ∪ L) :=
    M.subset_closure_of_subset' Set.subset_union_right hL.1.subset_ground
  rcases (separation_hyperplanes hW hY hd).2 _ hJ hmJ with h | h
  · exact Or.inl (hLJ.trans_eq h)
  · exact Or.inr (hLJ.trans_eq h)

/-- B.25: every corank-two flat above D lies in W, Y or T. -/
theorem corankTwo_below_three_planes {D L W Y T : Set α}
    (hD : M.IsFlat D) (hrD : natRank M D + 4 = natRank M M.E)
    (hL : CorankTwo M L) (hDL : D ⊆ L)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hT : IsHyperplane M T)
    (hDW : D ⊆ W) (hDY : D ⊆ Y) (hDT : D ⊆ T)
    (hcWY : CorankTwo M (W ∩ Y)) (hdWY : ¬ Indecomposable M (W ∩ Y))
    (hcWT : CorankTwo M (W ∩ T)) (hdWT : ¬ Indecomposable M (W ∩ T))
    (hcYT : CorankTwo M (Y ∩ T)) (hdYT : ¬ Indecomposable M (Y ∩ T)) :
    L ⊆ W ∨ L ⊆ Y ∨ L ⊆ T := by
  have hrL := corankTwo_natRank hL
  have hnLD : ¬ L ⊆ D := by intro h; have := natRank_mono (M := M) h; omega
  obtain ⟨e,heL,heD⟩ := Set.not_subset.mp hnLD
  let P := M.closure (insert e D)
  have hP : M.IsFlat P := M.isFlat_closure _
  have hDP : D ⊆ P := M.subset_closure_of_subset' (Set.subset_insert e D) hD.subset_ground
  have hPL : P ⊆ L := (M.closure_mono (Set.insert_subset heL hDL)).trans_eq hL.1.closure
  have hrP : natRank M P = natRank M D + 1 := natRank_closure_insert hD (hL.1.subset_ground heL) heD
  have hrP' : natRank M P + 3 = natRank M M.E := by omega
  have hm := cover_below_pair_plane hD hP hDP hrP hW.1 hY.1 hT.1 hDW hDY hDT
    (separation_hyperplanes hW hY hdWY).1 (separation_hyperplanes hW hT hdWT).1
    (separation_hyperplanes hY hT hdYT).1
  rcases hm with hm | hm | hm
  · rcases corankTwo_below_one_of_pair hP hrP' hL hPL hm hW hY hcWY hdWY with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases corankTwo_below_one_of_pair hP hrP' hL hPL hm hW hT hcWT hdWT with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact Or.inr (corankTwo_below_one_of_pair hP hrP' hL hPL hm hY hT hcYT hdYT)
end TutteFormalization.Homotopy
