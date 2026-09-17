import TutteFormalization.Homotopy.RankTableEmbedding
import TutteFormalization.Homotopy.RankTwo

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

set_option maxRecDepth 100000 in
-- Finite extension/extraction in the six-label restriction, not an ambient claim.
theorem bipartite_small_extension : ∀ S : Finset (Fin 6), S.card ≤ 3 →
    ∃ B, S ⊆ B ∧ B.card = 4 ∧ B ∉ fourCircuits := by decide

set_option maxRecDepth 100000 in
theorem bipartite_large_basis : ∀ S : Finset (Fin 6), 4 < S.card →
    ∃ B, B ⊆ S ∧ B.card = 4 ∧ B ∉ fourCircuits := by decide

/-- The ambient geometry needed for a (2,1,1) four-set: a full decomposable
pair spans a corank-two flat, and the set escapes both hyperplanes above it. -/
theorem spans_of_decomposable_pair {P S X Y : Set α}
    (hP : CorankTwo M P) (hnP : ¬ Indecomposable M P)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hPX : P ⊆ X) (hPY : P ⊆ Y) (hSE : S ⊆ M.E)
    (hPS : P ⊆ M.closure S) (hnSX : ¬ S ⊆ X) (hnSY : ¬ S ⊆ Y) :
    M.closure S = M.E := by
  have hmeet := hyperplane_inter_eq_of_corankTwo hP hX hY hXY hPX hPY
  have hdec : ¬ Indecomposable M (X ∩ Y) := by simpa only [hmeet] using hnP
  by_contra hne
  have hstrict : ¬ M.E ⊆ M.closure S := fun h => hne
    (Set.Subset.antisymm (M.closure_subset_ground _) h)
  obtain ⟨e,heE,he⟩ := Set.not_subset.mp hstrict
  obtain ⟨H,hH,hSH,_⟩ := exists_hyperplane_superset_notMem (M.isFlat_closure _) heE he
  rcases (separation_hyperplanes hX hY hdec).2 H hH
    (by simpa only [hmeet] using hPS.trans hSH) with h | h
  · exact hnSX ((M.subset_closure _ hSE).trans (hSH.trans_eq h))
  · exact hnSY ((M.subset_closure _ hSE).trans (hSH.trans_eq h))

/-- Once the geometric four-set claims are proved, they determine every rank
of the selected restriction, including all smaller and larger subsets. -/
theorem bipartite_rank_table (e : Fin 6 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hM : natRank M M.E = 4)
    (hb : ∀ B : Finset (Fin 6), B.card = 4 → B ∉ fourCircuits →
      M.Indep (e '' (B : Set (Fin 6))))
    (hc : ∀ C ∈ fourCircuits, natRank M (e '' (C : Set (Fin 6))) = 3) :
    ∀ S : Finset (Fin 6), natRank M (e '' (S : Set (Fin 6))) = bipartiteModel.rank S := by
  have indep_rank : ∀ S : Finset (Fin 6), M.Indep (e '' (S : Set (Fin 6))) →
      natRank M (e '' (S : Set (Fin 6))) = S.card := by
    intro S hS
    rw [natRank_eq_ncard_of_isBasis hS.isBasis_self, Set.ncard_image_of_injective _ hinj]
    simp
  intro S
  change _ = bipartiteRank S
  unfold bipartiteRank
  split_ifs with hsmall hcirc
  · obtain ⟨B,hSB,hBc,hBn⟩ := bipartite_small_extension S hsmall
    exact indep_rank S ((hb B hBc hBn).subset (Set.image_mono hSB))
  · exact hc S hcirc
  · have hupper : natRank M (e '' (S : Set (Fin 6))) ≤ 4 := by
      have h := natRank_mono (M := M) (show e '' (S : Set (Fin 6)) ⊆ M.E by
        rintro _ ⟨i,_,rfl⟩; exact he i)
      omega
    by_cases hfour : S.card = 4
    · simpa only [hfour] using indep_rank S (hb S hfour hcirc)
    · obtain ⟨B,hBS,hBc,hBn⟩ := bipartite_large_basis S (by omega)
      have hr := indep_rank B (hb B hBc hBn)
      have hle := natRank_mono (M := M) (Set.image_mono (f := e) (show (B : Set (Fin 6)) ⊆ S from hBS))
      omega

/-- Concrete fourth-model embedding from a verified basis/circuit description. -/
noncomputable def fourthModelOfBases (e : Fin 6 → α) (he : ∀ i, e i ∈ M.E)
    (hinj : Function.Injective e) (hM : natRank M M.E = 4)
    (hb : ∀ B : Finset (Fin 6), B.card = 4 → B ∉ fourCircuits →
      M.Indep (e '' (B : Set (Fin 6))))
    (hc : ∀ C ∈ fourCircuits, natRank M (e '' (C : Set (Fin 6))) = 3) :
    ModelEmbedding bipartiteModel M :=
  ModelEmbedding.ofRankTable e he (bipartite_rank_table e he hinj hM hb hc) (by
    apply flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) M.ground_isFlat
      (M.closure_subset_ground _)
    rw [natRank_closure,bipartite_rank_table e he hinj hM hb hc,hM]
    decide)
end TutteFormalization.Homotopy
