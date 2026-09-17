import TutteFormalization.Separation
import TutteFormalization.Homotopy.Cancellation

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {H K F : Set α}

theorem hyperplane_not_subset (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hne : H ≠ K) : ¬ H ⊆ K := by
  intro h
  exact hne ((hH.2.2 K hK.1 h).resolve_right hK.2.1).symm

/-- B.1's separation argument identifies the two separation sides with H and K. -/
theorem separation_hyperplanes (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hn : ¬ Indecomposable M (H ∩ K)) :
    H ∪ K = M.E ∧ ∀ Q, IsHyperplane M Q → H ∩ K ⊆ Q → Q = H ∨ Q = K := by
  obtain ⟨A,B,hI,hU,hnA,hnB,hs⟩ :=
    (decomposable_iff_separation (flat_inter hH.1 hK.1)).mp hn
  have hAHorBH := hs H hH Set.inter_subset_left
  have hAKorBK := hs K hK Set.inter_subset_right
  have sameA (hAH : A ⊆ H) (hAK : A ⊆ K) : False :=
    hnA ((Set.subset_inter hAH hAK).antisymm (hI ▸ Set.inter_subset_left))
  have sameB (hBH : B ⊆ H) (hBK : B ⊆ K) : False :=
    hnB ((Set.subset_inter hBH hBK).antisymm (hI ▸ Set.inter_subset_right))
  have cross {A B : Set α} (hi : H ∩ K = A ∩ B) (hu : A ∪ B = M.E)
      (hAH : A ⊆ H) (hBK : B ⊆ K) : H = A ∧ K = B := by
    constructor
    · apply Set.Subset.antisymm _ hAH
      intro e he
      rcases hu.symm ▸ hH.1.subset_ground he with ha | hb
      · exact ha
      · exact (hi ▸ (show e ∈ H ∩ K from ⟨he,hBK hb⟩)).1
    · apply Set.Subset.antisymm _ hBK
      intro e he
      rcases hu.symm ▸ hK.1.subset_ground he with ha | hb
      · exact (hi ▸ (show e ∈ H ∩ K from ⟨hAH ha,he⟩)).2
      · exact hb
  have hs' : H ∪ K = M.E ∧ ∀ Q, IsHyperplane M Q → H ∩ K ⊆ Q → H ⊆ Q ∨ K ⊆ Q := by
    rcases hAHorBH with hAH | hBH <;> rcases hAKorBK with hAK | hBK
    · exact False.elim (sameA hAH hAK)
    · obtain ⟨rfl,rfl⟩ := cross hI hU hAH hBK
      exact ⟨hU,hs⟩
    · obtain ⟨ha,hb⟩ := cross (hI.trans (Set.inter_comm A B))
        ((Set.union_comm B A).trans hU) hBH hAK
      refine ⟨by simpa only [ha,hb,Set.union_comm] using hU, ?_⟩
      intro Q hQ hIQ
      simpa only [ha,hb,or_comm] using hs Q hQ hIQ
    · exact False.elim (sameB hBH hBK)
  refine ⟨hs'.1, ?_⟩
  intro Q hQ hIQ
  rcases hs'.2 Q hQ hIQ with hHQ | hKQ
  · exact Or.inl ((hH.2.2 Q hQ.1 hHQ).resolve_right hQ.2.1)
  · exact Or.inr ((hK.2.2 Q hQ.1 hKQ).resolve_right hQ.2.1)

/-- B.1: the two residual hyperplanes form a rank-additive ground partition. -/
theorem decomposable_inter_corankTwo (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hne : H ≠ K) (hn : ¬ Indecomposable M (H ∩ K)) : CorankTwo M (H ∩ K) := by
  let F := H ∩ K
  have hF : M.IsFlat F := flat_inter hH.1 hK.1
  obtain ⟨hu, hall⟩ := separation_hyperplanes hH hK hn
  have hH' := hyperplane_sdiff_contract hF hH Set.inter_subset_left
  have hK' := hyperplane_sdiff_contract hF hK Set.inter_subset_right
  have hd : Disjoint (H \ F) (K \ F) := by
    apply Set.disjoint_left.mpr
    intro e he hk
    exact he.2 ⟨he.1,hk.1⟩
  have hu' : (H \ F) ∪ (K \ F) = (M ／ F).E := by
    change (H \ F) ∪ (K \ F) = M.E \ F
    rw [← Set.union_sdiff_distrib,hu]
  have hr := natRank_add_of_hyperplane_sides hd hu' (by
    intro Q hQ
    have hQl := hyperplane_union_of_contract hF hQ
    rcases hall (Q ∪ F) hQl Set.subset_union_right with heq | heq
    · left
      intro e he
      exact ((heq.symm ▸ he.1 : e ∈ Q ∪ F)).resolve_right he.2
    · right
      intro e he
      exact ((heq.symm ▸ he.1 : e ∈ Q ∪ F)).resolve_right he.2)
  have hrH := hyperplane_natRank hH'
  have hrK := hyperplane_natRank hK'
  have htotal := natRank_contract_add F (M.E \ F) hF.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset hF.subset_ground] at htotal
  have htwo : natRank M F + 2 = natRank M M.E := by
    change natRank (M ／ F) (M ／ F).E + natRank M F = natRank M M.E at htotal
    omega
  refine ⟨hF, ?_⟩
  rw [← cast_natRank M F, ← cast_natRank M M.E]
  exact_mod_cast htwo

/-- For an edge, covering the ground by its endpoints would separate the quotient. -/
theorem adjacent_union_ne_ground (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (he : TutteAdjacent M H K) : H ∪ K ≠ M.E := by
  intro hu
  let F := H ∩ K
  have hF : M.IsFlat F := he.2.1.1
  have hH' := hyperplane_sdiff_contract hF hH Set.inter_subset_left
  have hK' := hyperplane_sdiff_contract hF hK Set.inter_subset_right
  have hHn : (H \ F).Nonempty := Set.not_subset.mp (by
    intro h; exact hyperplane_not_subset hH hK he.1 (h.trans Set.inter_subset_right))
  have hKn : (K \ F).Nonempty := Set.not_subset.mp (by
    intro h; exact hyperplane_not_subset hK hH he.1.symm (h.trans Set.inter_subset_left))
  apply connected_iff_no_natRank_partition.mp he.2.1.2
  refine ⟨H \ F,K \ F,hHn,hKn,?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hk
    exact he.2 ⟨he.1,hk.1⟩
  · change (H \ F) ∪ (K \ F) = M.E \ F
    rw [← Set.union_sdiff_distrib,hu]
  · have hc : natRank M F + 2 = natRank M M.E := by
      have hr := he.2.2.2
      rw [← cast_natRank M F, ← cast_natRank M M.E] at hr
      exact_mod_cast hr
    have htotal := natRank_contract_add F (M.E \ F) hF.subset_ground Set.Subset.rfl
    rw [Set.sdiff_union_of_subset hF.subset_ground] at htotal
    change natRank (M ／ F) (M ／ F).E + natRank M F = natRank M M.E at htotal
    have hrH := hyperplane_natRank hH'
    have hrK := hyperplane_natRank hK'
    simp only [F] at *
    omega

theorem corankTwo_natRank (hF : CorankTwo M F) : natRank M F + 2 = natRank M M.E := by
  have h := hF.2
  rw [← cast_natRank M F, ← cast_natRank M M.E] at h
  exact_mod_cast h

theorem corankTwo_hyperplane_pair (hF : CorankTwo M F) :
    ∃ H K, IsHyperplane M H ∧ IsHyperplane M K ∧ H ≠ K ∧ F ⊆ H ∧ F ⊆ K := by
  have hr := corankTwo_natRank hF
  have hn : ¬ M.E ⊆ F := by
    intro h
    have := natRank_mono (M := M) h
    omega
  obtain ⟨e,heE,heF⟩ := Set.not_subset.mp hn
  obtain ⟨H,hH,hFH,_⟩ := exists_hyperplane_superset_notMem hF.1 heE heF
  have hrH := hyperplane_natRank hH
  have hnH : ¬ H ⊆ F := by
    intro h
    have := natRank_mono (M := M) h
    omega
  obtain ⟨f,hfH,hfF⟩ := Set.not_subset.mp hnH
  obtain ⟨K,hK,hFK,hfK⟩ := exists_hyperplane_superset_notMem hF.1 (hH.1.subset_ground hfH) hfF
  exact ⟨H,K,hH,hK,(fun h => hfK (h ▸ hfH)),hFH,hFK⟩

/-- The rank-two characterization in Section 1.3, with explicit three witnesses. -/
theorem corankTwo_indecomposable_iff_three (hF : CorankTwo M F) :
    Indecomposable M F ↔ ∃ H K Q, IsHyperplane M H ∧ IsHyperplane M K ∧
      IsHyperplane M Q ∧ H ≠ K ∧ H ≠ Q ∧ K ≠ Q ∧ F ⊆ H ∧ F ⊆ K ∧ F ⊆ Q := by
  constructor
  · intro hI
    obtain ⟨H,K,hH,hK,hHK,hFH,hFK⟩ := corankTwo_hyperplane_pair hF
    have hedge := tutteAdjacent_of_corankTwo hI hF hH hK hHK hFH hFK
    have hn : ¬ M.E ⊆ H ∪ K := by
      intro h
      exact adjacent_union_ne_ground hH hK hedge
        ((Set.union_subset hH.1.subset_ground hK.1.subset_ground).antisymm h)
    obtain ⟨e,heE,heHK⟩ := Set.not_subset.mp hn
    have heF : e ∉ F := fun h => heHK (Or.inl (hFH h))
    let Q := M.closure (insert e F)
    have hrQ : natRank M Q = natRank M F + 1 := by
      have hr := M.eRk_insert_eq_add_one (X := F) ⟨heE, by simpa only [hF.1.closure] using heF⟩
      rw [← cast_natRank M (insert e F), ← cast_natRank M F] at hr
      simpa only [Q,natRank_closure] using (show natRank M (insert e F) = natRank M F + 1 by exact_mod_cast hr)
    have hQ : IsHyperplane M Q := isHyperplane_of_natRank (M.isFlat_closure _) (by
      have := corankTwo_natRank hF; omega)
    have heQ : e ∈ Q := M.subset_closure _ (Set.insert_subset heE hF.1.subset_ground)
      (Set.mem_insert e F)
    have hFQ : F ⊆ Q := (Set.subset_insert e F).trans
      (M.subset_closure _ (Set.insert_subset heE hF.1.subset_ground))
    exact ⟨H,K,Q,hH,hK,hQ,hHK,(fun h => heHK (Or.inl (h ▸ heQ))),
      (fun h => heHK (Or.inr (h ▸ heQ))),hFH,hFK,hFQ⟩
  · rintro ⟨H,K,Q,hH,hK,hQ,hHK,hHQ,hKQ,hFH,hFK,hFQ⟩
    by_contra hn
    have hi := hyperplane_inter_eq_of_corankTwo hF hH hK hHK hFH hFK
    have hn' : ¬ Indecomposable M (H ∩ K) := by simpa only [hi] using hn
    rcases (separation_hyperplanes hH hK hn').2 Q hQ (hi ▸ hFQ) with h | h
    · exact hHQ h.symm
    · exact hKQ h.symm
end TutteFormalization.Homotopy
