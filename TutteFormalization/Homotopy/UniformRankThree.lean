import TutteFormalization.Homotopy.RankTableEmbedding

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Three distinct labels spanning rank three form a basis and realize the
approved U(3,3) model. All subsets inherit their actual matroid independence. -/
theorem rankThree_label_table (e : Fin 3 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hrM : natRank M M.E = 3)
    (hspan : M.closure (e '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = M.E)
    (S : Finset (Fin 3)) : natRank M (e '' (S : Set (Fin 3))) = u33.rank S := by
  classical
  have hall : M.Indep (e '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) := by
    apply M.indep_iff_eRk_eq_encard.mpr
    rw [← M.eRk_closure_eq,hspan,← cast_natRank M M.E,hrM,hinj.encard_image]
    simp
  have hs := hall.subset (Set.image_mono (f := e) (show (S : Set (Fin 3)) ⊆ ↑(Finset.univ : Finset (Fin 3)) by simp))
  have hr := natRank_eq_ncard_of_isBasis hs.isBasis_self
  rw [Set.ncard_image_of_injective _ hinj,Set.ncard_coe_finset] at hr
  have hc : S.card ≤ 3 := by simpa using Finset.card_le_univ S
  change _ = min S.card 3
  rw [Nat.min_eq_left hc]
  exact hr

noncomputable def rankThreeModel (e : Fin 3 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hrM : natRank M M.E = 3)
    (hspan : M.closure (e '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = M.E) :
    ModelEmbedding u33 M :=
  ModelEmbedding.ofRankTable e he (rankThree_label_table e he hinj hrM hspan) hspan
end TutteFormalization.Homotopy
