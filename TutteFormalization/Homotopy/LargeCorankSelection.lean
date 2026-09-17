import TutteFormalization.Homotopy.PreferredHyperplane

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Source Case 2.3's Chain choice, with both strict inclusions proved. -/
theorem exists_corankThree_between {F A : Set α} (hF : Indecomposable M F)
    (hA : Indecomposable M A) (hcA : CorankTwo M A) (hFA : F ⊆ A)
    (hrF : natRank M F + 4 ≤ natRank M M.E) :
    ∃ K, Indecomposable M K ∧ F ⊂ K ∧ K ⊂ A ∧ natRank M K + 3 = natRank M M.E := by
  have hrA := corankTwo_natRank hcA
  obtain ⟨K,hK,hFK,hKA,hrK⟩ := exists_indecomposable_of_rank hA hF hFA
    (natRank M M.E-3) (by omega) (by omega)
  have hrK' : natRank M K + 3 = natRank M M.E := by omega
  refine ⟨K,hK,Set.ssubset_iff_subset_ne.mpr ⟨hFK,?_⟩,
    Set.ssubset_iff_subset_ne.mpr ⟨hKA,?_⟩,hrK'⟩
  · intro he; have hh := congrArg (natRank M) he; omega
  · intro he; have hh := congrArg (natRank M) he; omega

/-- A corank-two flat and an escaping flat inside a hyperplane span that
hyperplane. This supplies the Complement join premise in Case 2.3. -/
theorem join_eq_hyperplane_of_escape {Q K H : Set α} (hQ : CorankTwo M Q)
    (hK : M.IsFlat K) (hH : IsHyperplane M H) (hQH : Q ⊆ H) (hKH : K ⊆ H)
    (hne : ¬ K ⊆ Q) : M.closure (Q ∪ K) = H := by
  have hQJ : Q ⊆ M.closure (Q ∪ K) := M.subset_closure_of_subset' Set.subset_union_left hQ.1.subset_ground
  have hKJ : K ⊆ M.closure (Q ∪ K) := M.subset_closure_of_subset' Set.subset_union_right hK.subset_ground
  have hs : Q ⊂ M.closure (Q ∪ K) := Set.ssubset_iff_subset_ne.mpr
    ⟨hQJ,fun he => hne (hKJ.trans_eq he.symm)⟩
  have hlo := natRank_lt_of_flat_ssubset hQ.1 (M.isFlat_closure _) hs
  have hrQ := corankTwo_natRank hQ
  have hrH := hyperplane_natRank hH
  exact flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) hH.1
    ((M.closure_mono (Set.union_subset hQH hKH)).trans_eq hH.1.closure) (by omega)
end TutteFormalization.Homotopy
