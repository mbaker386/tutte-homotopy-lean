import TutteFormalization.Homotopy.OffHyperplaneChoice
import TutteFormalization.RelativeComplement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- A hyperplane cutting a one-rank flat extension recovers its bottom and
forms a modular pair. Used in B.19 and the later maximal-G argument. -/
theorem hyperplane_inter_of_cover {F T H : Set α}
    (hF : M.IsFlat F) (hT : M.IsFlat T) (hH : IsHyperplane M H)
    (hFT : F ⊆ T) (hFH : F ⊆ H) (hrT : natRank M T = natRank M F + 1)
    (hnTH : ¬ T ⊆ H) : T ∩ H = F ∧ ModularPair M T H := by
  have hn : T ∩ H ≠ T := fun heq => hnTH (heq.symm.subset.trans Set.inter_subset_right)
  have hlt := natRank_lt_of_flat_ssubset (flat_inter hT hH.1) hT
    (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,hn⟩)
  have heq := (flat_eq_of_subset_of_natRank_le hF (flat_inter hT hH.1)
    (Set.subset_inter hFT hFH) (by omega)).symm
  have hj : M.closure (T ∪ H) = M.E := by
    have hHJ : H ⊆ M.closure (T ∪ H) := M.subset_closure_of_subset' Set.subset_union_right hH.1.subset_ground
    have hTJ : T ⊆ M.closure (T ∪ H) := M.subset_closure_of_subset' Set.subset_union_left hT.subset_ground
    rcases hH.2.2 _ (M.isFlat_closure _) hHJ with h | h
    · exact False.elim (hnTH (hTJ.trans_eq h))
    · exact h
  refine ⟨heq,hT,hH.1,?_⟩
  rw [heq,hj,← cast_natRank M T,← cast_natRank M H,← cast_natRank M F,← cast_natRank M M.E]
  have hh := hyperplane_natRank hH
  exact_mod_cast (show natRank M T + natRank M H = natRank M F + natRank M M.E by omega)

/-- A modular cut containing the top is determined by its hyperplanes.
The top premise matters for the allowed empty cut; it is automatic after cutPlus. -/
theorem cut_mem_of_all_hyperplanes (hΓ : ModularCut M Γ) (htop : M.E ∈ Γ)
    {F : Set α} (hF : M.IsFlat F)
    (hall : ∀ H, IsHyperplane M H → F ⊆ H → H ∈ Γ) : F ∈ Γ := by
  generalize hn : natRank M M.E - natRank M F = n
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases hFE : F = M.E
    · exact hFE ▸ htop
    have hnEF : ¬ M.E ⊆ F := fun h => hFE (Set.Subset.antisymm hF.subset_ground h)
    obtain ⟨e,heE,heF⟩ := Set.not_subset.mp hnEF
    let G := M.closure (insert e F)
    have hG : M.IsFlat G := M.isFlat_closure _
    have hFG : F ⊆ G := M.subset_closure_of_subset' (Set.subset_insert e F) hF.subset_ground
    have hrG : natRank M G = natRank M F + 1 := natRank_closure_insert hF heE heF
    have hGE := natRank_mono (M := M) hG.subset_ground
    have hmemG := ih (natRank M M.E - natRank M G) (by omega) hG
      (fun H hH hGH => hall H hH (hFG.trans hGH)) rfl
    obtain ⟨H,hH,hFH,heH⟩ := exists_hyperplane_superset_notMem hF heE heF
    have hnGH : ¬ G ⊆ H := fun h => heH (h
      (M.subset_closure _ (Set.insert_subset heE hF.subset_ground) (Set.mem_insert e F)))
    obtain ⟨hmeet,hmod⟩ := hyperplane_inter_of_cover hF hG hH hFG hFH hrG hnGH
    exact hmeet ▸ hΓ.inter_mem G H hmemG (hall H hH hFH) hmod

/-- For proper flats no nonempty-cut premise is needed. -/
theorem proper_cut_mem_of_all_hyperplanes (hΓ : ModularCut M Γ)
    {F : Set α} (hF : M.IsFlat F) (hne : F ≠ M.E)
    (hall : ∀ H, IsHyperplane M H → F ⊆ H → H ∈ Γ) : F ∈ Γ := by
  obtain ⟨e,heE,heF⟩ := Set.not_subset.mp (show ¬ M.E ⊆ F from fun h =>
    hne (Set.Subset.antisymm hF.subset_ground h))
  obtain ⟨H,hH,hFH,_⟩ := exists_hyperplane_superset_notMem hF heE heF
  exact cut_mem_of_all_hyperplanes hΓ
    (hΓ.upward H M.E (hall H hH hFH) M.ground_isFlat hH.1.subset_ground) hF hall
end TutteFormalization.Homotopy
