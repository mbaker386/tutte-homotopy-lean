import TutteFormalization.Homotopy.LargeCorankSelection

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The previously implicit Complement join premise in source Case 2.3.
The selected K cannot lie in the outgoing intersection Q, so K∨Q is the
bad hyperplane; that hyperplane cannot equal T, which contains G. -/
theorem large_complement_join {F G K H B J T : Set α}
    (hB : IsHyperplane M B) (hT : IsHyperplane M T)
    (hQ : CorankTwo M (B ∩ J)) (hK : M.IsFlat K)
    (hF : F = H ∩ B ∩ J) (hFK : F ⊂ K) (hKA : K ⊆ H ∩ B)
    (hKT : K ⊆ T) (hGT : G ⊆ T) (hGB : ¬ G ⊆ B) :
    M.closure ((B ∩ J) ∪ T) = M.E := by
  have hnKQ : ¬ K ⊆ B ∩ J := by
    intro hh
    apply hFK.2
    intro x hx
    rw [hF]
    exact ⟨hKA hx,(hh hx).2⟩
  have hj := join_eq_hyperplane_of_escape hQ hK hB Set.inter_subset_left
    (hKA.trans Set.inter_subset_right) hnKQ
  have hnQT : ¬ B ∩ J ⊆ T := by
    intro hh
    have hBT : B ⊆ T := by rw [← hj]; exact (M.closure_mono (Set.union_subset hh hKT)).trans_eq hT.1.closure
    have hrB := hyperplane_natRank hB
    have hrT := hyperplane_natRank hT
    have he := flat_eq_of_subset_of_natRank_le hB.1 hT.1 hBT (by omega)
    exact hGB (hGT.trans_eq he.symm)
  have hTJ : T ⊆ M.closure ((B ∩ J) ∪ T) := M.subset_closure_of_subset' Set.subset_union_right hT.1.subset_ground
  rcases hT.2.2 _ (M.isFlat_closure _) hTJ with he | he
  · exact False.elim (hnQT ((M.subset_closure_of_subset' Set.subset_union_left hQ.1.subset_ground).trans_eq he))
  · exact he

/-- Apply the verified Complement theorem to [Q,T,F], including the rank-one
extension and the join-to-ground certificate required later in Case 2.3. -/
theorem exists_large_complement {F Q T : Set α} (hF : Indecomposable M F)
    (hQ : Indecomposable M Q) (hT : IsHyperplane M T)
    (hFQ : F ⊆ Q) (hFT : F ⊆ T) (hjoin : M.closure (Q ∪ T) = M.E) :
    ∃ P, Indecomposable M P ∧ F ⊂ P ∧ P ⊆ Q ∧
      M.closure (P ∪ T) = M.E ∧ natRank M P = natRank M F + 1 := by
  obtain ⟨P,hP,hFP,hPQ,hPT,hr⟩ := exists_indecomposable_complement hQ hF hT.1 hFQ hFT hjoin
  have hrT := hyperplane_natRank hT
  have hFle := natRank_mono (M := M) hFT
  have hPle := natRank_mono (M := M) hP.1.subset_ground
  have hrP : natRank M P = natRank M F + 1 := by omega
  refine ⟨P,hP,Set.ssubset_iff_subset_ne.mpr ⟨hFP,?_⟩,hPQ,hPT,hrP⟩
  intro he
  have hh := congrArg (natRank M) he
  omega
end TutteFormalization.Homotopy
