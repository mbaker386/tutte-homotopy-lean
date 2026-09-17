import TutteFormalization.Homotopy.Context

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {H K : Set α}

/-- The selected U(2,2) diamond determined by a valid edge. -/
noncomputable def edgeEmbedding (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hedge : TutteAdjacent M H K) : ModelEmbedding u22 M := by
  classical
  let f : Finset (Fin 2) → Set α := fun S =>
    if S = ∅ then H ∩ K else if S = {0} then H else if S = {1} then K else M.E
  have hHK : ¬ H ⊆ K := by
    intro h
    exact hedge.1 ((hH.2.2 K hK.1 h).resolve_right hK.2.1).symm
  have hKH : ¬ K ⊆ H := by
    intro h
    exact hedge.1 ((hK.2.2 H hH.1 h).resolve_right hH.2.1)
  have hEH : ¬ M.E ⊆ H := fun h => hH.2.1 (hH.1.subset_ground.antisymm h)
  have hEK : ¬ M.E ⊆ K := fun h => hK.2.1 (hK.1.subset_ground.antisymm h)
  have hjoin : M.closure (H ∪ K) = M.E := by
    have hHC : H ⊆ M.closure (H ∪ K) := Set.subset_union_left.trans
      (M.subset_closure _ (Set.union_subset hH.1.subset_ground hK.1.subset_ground))
    rcases hH.2.2 _ (M.isFlat_closure _) hHC with heq | heq
    · apply False.elim
      apply hKH
      rw [← heq]
      exact Set.subset_union_right.trans
        (M.subset_closure _ (Set.union_subset hH.1.subset_ground hK.1.subset_ground))
    · exact heq
  have hrH := hyperplane_natRank hH
  have hrK := hyperplane_natRank hK
  have hrI : natRank M (H ∩ K) + 2 = natRank M M.E := by
    have h := hedge.2.2.2
    rw [← cast_natRank M (H ∩ K), ← cast_natRank M M.E] at h
    exact_mod_cast h
  have cases2 : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0,1} := by decide
  have cl2 : ∀ S, u22.closure S = S := by decide
  have hne01 : ({0,1} : Finset (Fin 2)) ≠ {0} := by decide
  have hne10 : ({1,0} : Finset (Fin 2)) ≠ {0} := by decide
  have hne11 : ({1,0} : Finset (Fin 2)) ≠ {1} := by decide
  have hIE := hedge.2.1.1.subset_ground
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases cases2 S with rfl | rfl | rfl | rfl <;> simp [hne01, hne10, hne11, hIE, f] <;>
      first | exact hH.1 | exact hK.1 | exact hedge.2.1.1 | exact M.ground_isFlat
  · intro S T hS hT
    rcases cases2 S with rfl | rfl | rfl | rfl <;>
      rcases cases2 T with rfl | rfl | rfl | rfl <;>
      simp [hne01, hne10, hne11, hIE, f, hHK, hKH, hEH, hEK, Set.subset_inter_iff,
        hH.1.subset_ground, hK.1.subset_ground]
  · intro S T hS hT
    rcases cases2 S with rfl | rfl | rfl | rfl <;>
      rcases cases2 T with rfl | rfl | rfl | rfl <;>
      simp [hne01, hne10, hne11, hIE, f, cl2, hjoin, Set.union_comm K H,
        hH.1.closure, hK.1.closure, hedge.2.1.1.closure, M.ground_isFlat.closure,
        Set.union_eq_right.mpr hH.1.subset_ground,
        Set.union_eq_right.mpr hK.1.subset_ground,
        Set.union_eq_left.mpr hH.1.subset_ground,
        Set.union_eq_left.mpr hK.1.subset_ground,
        Set.union_eq_right.mpr hIE, Set.union_eq_left.mpr hIE,
        Set.union_eq_right.mpr (Set.inter_subset_left : H ∩ K ⊆ H),
        Set.union_eq_right.mpr (Set.inter_subset_right : H ∩ K ⊆ K),
        Set.union_eq_left.mpr (Set.inter_subset_left : H ∩ K ⊆ H),
        Set.union_eq_left.mpr (Set.inter_subset_right : H ∩ K ⊆ K)]
  · have ht : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
    simp [hne01, hne10, hne11, hIE, f, ht]
  · intro S hS
    rcases cases2 S with rfl | rfl | rfl | rfl <;> simp [hne01, hne10, hne11, hIE, f, u22, uniformRank] <;> omega

/-- The literal three-vertex backtrack; no duplicate adjacent vertices removed. -/
def backtrack (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hedge : TutteAdjacent M H K) : TuttePath M where
  length := 2
  vertex := ![H,K,H]
  isHyperplane i := by fin_cases i <;> first | exact hH | exact hK
  adjacent i := by fin_cases i <;> first | exact hedge | exact hedge.symm

theorem backtrack_elementary {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hedge : TutteAdjacent M H K)
    (hoffH : H ∉ Γ) (hoffK : K ∉ Γ) : Elementary M Γ (backtrack hH hK hedge) := by
  classical
  have hHplus := (hyperplane_off_cutPlus hH).mpr hoffH
  have hKplus := (hyperplane_off_cutPlus hK).mpr hoffK
  have hIplus : H ∩ K ∉ cutPlus M Γ := by
    intro h
    exact hHplus ((cutPlus_modular hΓ).upward _ H h hH.1 Set.inter_subset_left)
  have hIoff : H ∩ K ∉ Γ := fun h => hIplus (Or.inl h)
  have hIne : H ∩ K ≠ M.E := fun h => hIplus (Or.inr h)
  have flat2 : ∀ S, u22.Flat S := by decide
  have cases2 : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0,1} := by decide
  have hne01 : ({0,1} : Finset (Fin 2)) ≠ {0} := by decide
  refine Elementary.base (BaseElementary.first (edgeEmbedding hH hK hedge)
    (backtrack hH hK hedge) ?_ ?_ ?_ rfl ?_)
  · ext S
    rcases cases2 S with rfl | rfl | rfl | rfl <;>
      simp [ExactCut, ModelEmbedding.InducedCut, edgeEmbedding, flat2, hne01,
        hHplus, hKplus, hIplus, cutPlus, Finset.univ_fin2, hIoff, hIne,
        hoffH, hoffK, hH.2.1, hK.2.1,
        show (∅ : Finset (Fin 2)) ≠ {0,1} by decide,
        show ({0} : Finset (Fin 2)) ≠ {0,1} by decide,
        show ({1} : Finset (Fin 2)) ≠ {0,1} by decide]
  · simpa [edgeEmbedding] using hedge.2.1
  · simp [TuttePath.word, backtrack, List.ofFn_succ, edgeEmbedding]
  · intro i
    fin_cases i <;> first | exact hHplus | exact hKplus

theorem backtrack_null {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hedge : TutteAdjacent M H K)
    (hoffH : H ∉ Γ) (hoffK : K ∉ Γ) : NullHomotopic M Γ (backtrack hH hK hedge) :=
  elementary_null (backtrack_elementary hΓ hH hK hedge hoffH hoffK)
end TutteFormalization.Homotopy
