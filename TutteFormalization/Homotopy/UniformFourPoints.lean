import TutteFormalization.Homotopy.UniformRankThree

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Four distinct labels in rank three with every triple spanning realize
the actual U(3,4) rank table needed by the third-kind recognition. -/
theorem rankFourPoints_label_table (e : Fin 4 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hrM : natRank M M.E = 3)
    (hspan : ∀ T : Finset (Fin 4), T.card = 3 → M.closure (e '' (T : Set (Fin 4))) = M.E)
    (S : Finset (Fin 4)) : natRank M (e '' (S : Set (Fin 4))) = u34.rank S := by
  classical
  have hIndep (T : Finset (Fin 4)) (hT : T.card = 3) : M.Indep (e '' (T : Set (Fin 4))) := by
    apply M.indep_iff_eRk_eq_encard.mpr
    rw [← M.eRk_closure_eq,hspan T hT,← cast_natRank M M.E,hrM,hinj.encard_image]
    simp [hT]
  change _ = min S.card 3
  by_cases hs : S.card ≤ 3
  · obtain ⟨T,hST,_,hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hs
      (show 3 ≤ (Finset.univ : Finset (Fin 4)).card by decide)
    have hh := (hIndep T hT).subset (Set.image_mono (Finset.coe_subset.mpr hST))
    have hr := natRank_eq_ncard_of_isBasis hh.isBasis_self
    rw [Set.ncard_image_of_injective _ hinj,Set.ncard_coe_finset] at hr
    simpa only [Nat.min_eq_left hs] using hr
  · obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
    have hrT : natRank M (e '' (T : Set (Fin 4))) = 3 := by
      rw [← natRank_closure,hspan T hT,hrM]
    have hlo := natRank_mono (M := M) (Set.image_mono (f := e) (Finset.coe_subset.mpr hTS))
    have hhi := natRank_mono (M := M) (show e '' (S : Set (Fin 4)) ⊆ M.E by rintro _ ⟨i,_,rfl⟩; exact he i)
    rw [Nat.min_eq_right (by omega)]
    omega

noncomputable def rankFourPointsModel (e : Fin 4 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hrM : natRank M M.E = 3)
    (hspan : ∀ T : Finset (Fin 4), T.card = 3 → M.closure (e '' (T : Set (Fin 4))) = M.E) :
    ModelEmbedding u34 M :=
  ModelEmbedding.ofRankTable e he (rankFourPoints_label_table e he hinj hrM hspan) (by
    have ht := hspan {0,1,2} (by decide)
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← ht]
    exact M.closure_mono (Set.image_mono (by simp)))
end TutteFormalization.Homotopy
