import TutteFormalization.Homotopy.Embedding

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}

/-- Membership in closure tested by insertion rank, for finite ground sets. -/
theorem mem_closure_iff_natRank_insert {e : α} {S : Set α} (he : e ∈ M.E)
    (hS : S ⊆ M.E) : e ∈ M.closure S ↔ natRank M (insert e S) = natRank M S := by
  constructor
  · intro h
    apply Nat.le_antisymm
    · simpa only [natRank_closure] using
        natRank_mono (M := M) (Set.insert_subset h (M.subset_closure _ hS))
    · exact natRank_mono (Set.subset_insert _ _)
  · intro hr
    by_contra hn
    have h := M.eRk_insert_eq_add_one ⟨he,hn⟩
    rw [← cast_natRank M (insert e S), ← cast_natRank M S,hr] at h
    have hh : natRank M S = natRank M S + 1 := by exact_mod_cast h
    omega

namespace ModelEmbedding
variable (e : Fin n → α) (he : ∀ i, e i ∈ M.E)
    (hr : ∀ S : Finset (Fin n), natRank M (e '' (S : Set (Fin n))) = N.rank S)

include he hr in
theorem label_mem_closure_iff (S : Finset (Fin n)) (i : Fin n) :
    e i ∈ M.closure (e '' (S : Set (Fin n))) ↔ i ∈ N.closure S := by
  rw [mem_closure_iff_natRank_insert (he i) (by rintro _ ⟨j,_,rfl⟩; exact he j)]
  have hins : insert (e i) (e '' (S : Set (Fin n))) = e '' (↑(insert i S) : Set (Fin n)) := by
    simp
  rw [hins,hr,hr]
  simp [FiniteModel.closure]

include he hr in
theorem closure_image_model_closure (S : Finset (Fin n)) :
    M.closure (e '' (N.closure S : Set (Fin n))) = M.closure (e '' (S : Set (Fin n))) := by
  apply Set.Subset.antisymm
  · apply M.closure_subset_closure_of_subset_closure
    rintro _ ⟨i,hi,rfl⟩
    exact (label_mem_closure_iff e he hr S i).mpr hi
  · apply M.closure_mono
    apply Set.image_mono
    rw [N.closure_eq]
    exact N.matroid.subset_closure _ (by simp)

/-- Recognition bridge: an actual spanning labelled restriction with the complete
finite rank table determines the approved join-preserving upper-sublattice model.
Its rank-table hypotheses must be proved from ambient geometry at each use. -/
noncomputable def ofRankTable
    (hspan : M.closure (e '' (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) = M.E) : ModelEmbedding N M where
  image F := M.closure (e '' (F : Set (Fin n)))
  image_flat _ _ := M.isFlat_closure _
  order_iff F G hF hG := by
    constructor
    · intro h i hi
      have hp : e i ∈ M.closure (e '' (G : Set (Fin n))) := h
        (M.subset_closure _ (by rintro _ ⟨j,_,rfl⟩; exact he j) ⟨i,hi,rfl⟩)
      have hm := (label_mem_closure_iff e he hr G i).mp hp
      rwa [hG] at hm
    · intro h
      exact M.closure_mono (Set.image_mono h)
  map_join F G _ _ := by
    rw [closure_image_model_closure e he hr]
    simp only [Finset.coe_union,Set.image_union]
    rw [M.closure_closure_union_closure_eq_closure_union]
  map_top := hspan
  relative_rank F _ := by
    rw [natRank_closure,hr,natRank_closure]
    simp [natRank]
end ModelEmbedding
end TutteFormalization.Homotopy
