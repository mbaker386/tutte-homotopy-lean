import TutteFormalization.Homotopy.UnionTransfer
import TutteFormalization.PathRanks

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.23's transfer argument proving the newly constructed corank-three flat
indecomposable. It follows the two common-trace non-cover arguments in the source. -/
theorem third_flat_indecomposable {W Y I G P Q L : Set α}
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hI : IsHyperplane M I)
    (hWY : W ≠ Y) (hmid : CorankTwo M (W ∩ Y)) (hdmid : ¬ Indecomposable M (W ∩ Y))
    (hdWI : ¬ Indecomposable M (W ∩ I)) (hdYI : ¬ Indecomposable M (Y ∩ I))
    (hG : M.IsFlat G) (hrG : natRank M G + 4 = natRank M M.E)
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E) (hGP : G ⊆ P) (hPm : P ⊆ W ∩ Y)
    (hQ : M.IsFlat Q) (hrQ : natRank M Q + 3 = natRank M M.E) (hGQ : G ⊆ Q) (hQm : Q ⊆ W ∩ Y)
    (hL : CorankTwo M L) (hGL : G ⊆ L) (hLI : L ⊆ I)
    (hjoin : M.closure (L ∪ (W ∩ Y)) = M.E) (hnPI : ¬ P ⊆ I) (hnQI : ¬ Q ⊆ I) :
    Indecomposable M Q := by
  have hrm := corankTwo_natRank hmid
  have hmeet := corankTwo_inter_eq_of_join_eq_ground hG hL hmid.1 hGL (hGP.trans hPm) (by omega) hjoin
  have hGP' : G ⊂ P := Set.ssubset_iff_subset_ne.mpr ⟨hGP,by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  have hGQ' : G ⊂ Q := Set.ssubset_iff_subset_ne.mpr ⟨hGQ,by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  obtain ⟨hH₁,hPmH⟩ := diamond_join_inter hmid.1 hL hP.1 hmeet hGP' hPm (by omega) (by omega) hjoin
  obtain ⟨hH₃,hQmH⟩ := diamond_join_inter hmid.1 hL hQ hmeet hGQ' hQm (by omega) (by omega) hjoin
  let H₁ := M.closure (L ∪ P)
  let H₃ := M.closure (L ∪ Q)
  have hLH₁ : L ⊆ H₁ := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hLH₃ : L ⊆ H₃ := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hPH₁ : P ⊆ H₁ := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  have hQH₃ : Q ⊆ H₃ := M.subset_closure_of_subset' Set.subset_union_right hQ.subset_ground
  have hnLW : ¬ L ⊆ W := by
    intro h
    have hEW : M.E ⊆ W := hjoin ▸
      (M.closure_mono (Set.union_subset h Set.inter_subset_left)).trans_eq hW.1.closure
    exact hW.2.1 (Set.Subset.antisymm hW.1.subset_ground hEW)
  have hnLY : ¬ L ⊆ Y := by
    intro h
    have hEY : M.E ⊆ Y := hjoin ▸
      (M.closure_mono (Set.union_subset h Set.inter_subset_right)).trans_eq hY.1.closure
    exact hY.2.1 (Set.Subset.antisymm hY.1.subset_ground hEY)
  have hWH₁ : W ≠ H₁ := fun h => hnLW (hLH₁.trans_eq h.symm)
  have hYH₁ : Y ≠ H₁ := fun h => hnLY (hLH₁.trans_eq h.symm)
  have hed := third_hyperplane_adjacent hP hrP hmid hdmid hPm hW hY hWY
    Set.inter_subset_left Set.inter_subset_right hH₁ hWH₁ hYH₁ hPH₁
  have hnH₁W := adjacent_union_ne_ground hH₁ hW hed.1
  have hnH₁Y := adjacent_union_ne_ground hH₁ hY hed.2
  have hIH₁ : I ≠ H₁ := fun h => hnPI (hPH₁.trans_eq h.symm)
  have hIH₃ : I ≠ H₃ := fun h => hnQI (hQH₃.trans_eq h.symm)
  have hi₁ := hyperplane_inter_eq_of_corankTwo hL hI hH₁ hIH₁ hLI hLH₁
  have hi₃ := hyperplane_inter_eq_of_corankTwo hL hI hH₃ hIH₃ hLI hLH₃
  have hWI := (separation_hyperplanes hW hI hdWI).1
  have hYI := (separation_hyperplanes hY hI hdYI).1
  have hnH₃W := noncover_of_same_trace hH₁.1.subset_ground hW.1.subset_ground hWI (hi₁.trans hi₃.symm) hnH₁W
  have hnH₃Y := noncover_of_same_trace hH₁.1.subset_ground hY.1.subset_ground hYI (hi₁.trans hi₃.symm) hnH₁Y
  have hconn := indecomposable_inter (hyperplane_indecomposable hW) (hyperplane_indecomposable hH₃)
    (by simpa only [Set.union_comm] using hnH₃W)
  have hno : (W ∩ H₃) ∪ Y ≠ M.E := by
    intro heq
    apply hnH₃Y
    apply Set.Subset.antisymm (Set.union_subset hH₃.1.subset_ground hY.1.subset_ground)
    rw [← heq]
    exact Set.union_subset_union Set.inter_subset_right Set.Subset.rfl
  have hconn' := indecomposable_inter hconn (hyperplane_indecomposable hY) hno
  have heq : (W ∩ H₃) ∩ Y = Q := by
    calc
      (W ∩ H₃) ∩ Y = (W ∩ Y) ∩ H₃ := by
        ext x
        exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
      _ = Q := hQmH
  exact heq ▸ hconn'
end TutteFormalization.Homotopy
