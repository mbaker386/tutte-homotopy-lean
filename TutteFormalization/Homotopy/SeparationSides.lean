import TutteFormalization.Homotopy.RankTwo

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {A B H K Q : Set α}

/-- In a loopless direct sum each full side is a flat. -/
theorem partition_side_isFlat (h0 : M.IsFlat ∅) (hd : Disjoint A B)
    (hu : A ∪ B = M.E) (hr : natRank M A + natRank M B = natRank M M.E) : M.IsFlat A := by
  have hAE : A ⊆ M.E := Set.subset_union_left.trans_eq hu
  have hAC : A ⊆ M.closure A := M.subset_closure A hAE
  have hsplit := natRank_partition hd hu hr (M.closure_subset_ground A)
  rw [Set.inter_eq_right.mpr hAC, natRank_closure] at hsplit
  apply M.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm _ hAC
  intro e he
  rcases hu.symm ▸ M.closure_subset_ground A he with ha | hb
  · exact ha
  · have hpos := natRank_pos_of_empty_isFlat h0
      (Set.inter_subset_left.trans (M.closure_subset_ground A))
      (show (M.closure A ∩ B).Nonempty from ⟨e,he,hb⟩)
    omega

/-- Positivity of the opposite side gives a hyperplane over a direct-sum side. -/
theorem partition_side_hyperplane (h0 : M.IsFlat ∅) (hd : Disjoint A B)
    (hu : A ∪ B = M.E) (hr : natRank M A + natRank M B = natRank M M.E)
    (hB : B.Nonempty) : ∃ H, IsHyperplane M H ∧ A ⊆ H := by
  obtain ⟨e,he⟩ := hB
  have heE : e ∈ M.E := hu ▸ (Or.inr he : e ∈ A ∪ B)
  obtain ⟨H,hH,hAH,_⟩ := exists_hyperplane_superset_notMem
    (partition_side_isFlat h0 hd hu hr) heE (fun h => Set.disjoint_left.mp hd h he)
  exact ⟨H,hH,hAH⟩

/-- Opposite full separation sides cannot be contracted to a connected quotient. -/
theorem opposite_partition_hyperplanes_decomposable (hd : Disjoint A B)
    (hu : A ∪ B = M.E) (hr : natRank M A + natRank M B = natRank M M.E)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hAH : A ⊆ H) (hBK : B ⊆ K) :
    ¬ Indecomposable M (H ∩ K) := by
  intro hI
  rcases connected_contract_partition_side hd hu hr hI.1.subset_ground hI.2 with ha | hb
  · exact hK.2.1 ((Set.Subset.antisymm hK.1.subset_ground (by
      rw [← hu]; exact Set.union_subset (ha.trans Set.inter_subset_right) hBK)))
  · exact hH.2.1 ((Set.Subset.antisymm hH.1.subset_ground (by
      rw [← hu]; exact Set.union_subset hAH (hb.trans Set.inter_subset_left))))

/-- Lift the preceding obstruction from the direct-sum separation of M/Q. -/
theorem opposite_contract_hyperplanes_decomposable (hQ : M.IsFlat Q)
    (hd : Disjoint A B) (hu : A ∪ B = (M ／ Q).E)
    (hr : natRank (M ／ Q) A + natRank (M ／ Q) B = natRank (M ／ Q) (M ／ Q).E)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hQH : Q ⊆ H) (hQK : Q ⊆ K)
    (hAH : A ⊆ H \ Q) (hBK : B ⊆ K \ Q) : ¬ Indecomposable M (H ∩ K) := by
  intro hI
  have hIc := (indecomposable_sdiff_contract_iff hI.1 (Set.subset_inter hQH hQK)).mpr hI
  have hn := opposite_partition_hyperplanes_decomposable hd hu hr
    (hyperplane_sdiff_contract hQ hH hQH) (hyperplane_sdiff_contract hQ hK hQK) hAH hBK
  apply hn
  have heq : (H ∩ K) \ Q = (H \ Q) ∩ (K \ Q) := by tauto_set
  simpa only [heq] using hIc

/-- HD-004: assign X to one side, then construct a hyperplane over the opposite
side. Opposite membership and decomposability are proved, not assumed of Y. -/
theorem exists_opposite_separation_hyperplane (hQ : M.IsFlat Q)
    (hnQ : ¬ Indecomposable M Q) (hH : IsHyperplane M H) (hQH : Q ⊆ H) :
    ∃ A B K, Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      A ∪ B = (M ／ Q).E ∧
      natRank (M ／ Q) A + natRank (M ／ Q) B = natRank (M ／ Q) (M ／ Q).E ∧
      A ⊆ H \ Q ∧ IsHyperplane M K ∧ Q ⊆ K ∧ B ⊆ K \ Q ∧
      H ≠ K ∧ ¬ Indecomposable M (H ∩ K) ∧ CorankTwo M (H ∩ K) := by
  have hnC : ¬ Connected (M ／ Q) := fun h => hnQ ⟨hQ,h⟩
  rw [connected_iff_no_natRank_partition,not_not] at hnC
  obtain ⟨A,B,hA,hB,hd,hu,hr⟩ := hnC
  have hHs := hyperplane_sdiff_contract hQ hH hQH
  have build {A B : Set α} (hA : A.Nonempty) (hB : B.Nonempty) (hd : Disjoint A B)
      (hu : A ∪ B = (M ／ Q).E)
      (hr : natRank (M ／ Q) A + natRank (M ／ Q) B = natRank (M ／ Q) (M ／ Q).E)
      (hAH : A ⊆ H \ Q) : ∃ K, IsHyperplane M K ∧ Q ⊆ K ∧ B ⊆ K \ Q ∧
        H ≠ K ∧ ¬ Indecomposable M (H ∩ K) ∧ CorankTwo M (H ∩ K) := by
    obtain ⟨K,hK,hBK⟩ := partition_side_hyperplane (contract_empty_isFlat hQ)
      hd.symm ((Set.union_comm B A).trans hu) (by omega) hA
    have hBE : B ⊆ M.E \ Q := Set.subset_union_right.trans_eq hu
    have hKdis : Disjoint K Q := Set.disjoint_left.mpr (fun e he => (hK.1.subset_ground he).2)
    have hKback : (K ∪ Q) \ Q = K := by
      ext e
      simp only [Set.mem_sdiff,Set.mem_union]
      constructor
      · rintro ⟨he | he,hn⟩
        · exact he
        · exact False.elim (hn he)
      · intro he; exact ⟨Or.inl he,(hK.1.subset_ground he).2⟩
    have hKL := hyperplane_union_of_contract hQ hK
    have hBK' : B ⊆ (K ∪ Q) \ Q := by simpa only [hKback] using hBK
    have hne : H ≠ K ∪ Q := by
      intro heq
      have hfull : (M ／ Q).E ⊆ H \ Q := by
        rw [← hu]; exact Set.union_subset hAH (by simpa only [← heq] using hBK')
      exact hHs.2.1 (hHs.1.subset_ground.antisymm hfull)
    have hdec := opposite_contract_hyperplanes_decomposable hQ hd hu hr hH hKL
      hQH Set.subset_union_right hAH hBK'
    exact ⟨K ∪ Q,hKL,Set.subset_union_right,hBK',hne,hdec,
      decomposable_inter_corankTwo hH hKL hne hdec⟩
  rcases hyperplane_contains_partition_side hd hu hr hHs with hAH | hBH
  · obtain ⟨K,hK⟩ := build hA hB hd hu hr hAH
    exact ⟨A,B,K,hd,hA,hB,hu,hr,hAH,hK⟩
  · obtain ⟨K,hK⟩ := build hB hA hd.symm ((Set.union_comm B A).trans hu) (by omega) hBH
    exact ⟨B,A,K,hd.symm,hB,hA,(Set.union_comm B A).trans hu,by omega,hBH,hK⟩
end TutteFormalization.Homotopy
