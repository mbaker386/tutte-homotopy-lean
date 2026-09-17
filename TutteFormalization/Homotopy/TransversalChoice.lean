import TutteFormalization.Homotopy.SpecialPoles
import TutteFormalization.Homotopy.OffHyperplaneChoice

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.17: the first Complement application [W,Y,D]. -/
theorem exists_typeA_under_W (s : SpecialData M Γ) :
    ∃ A, s.TypeA A ∧ A ⊆ s.W ∧ ¬ A ⊆ s.Y := by
  obtain ⟨A,hA,hDA,hAW,hAY,hAr⟩ := exists_indecomposable_complement
    (hyperplane_indecomposable s.hW) s.D_indec s.hY.1 s.D_subset_W s.D_subset_Y
    (hyperplane_join_eq_ground s.hW s.hY s.W_ne_Y)
  have hDr := natRank_mono (M := M) s.D_subset_Y
  have hArE := natRank_mono (M := M) hA.1.subset_ground
  have hYr := hyperplane_natRank s.hY
  have hAr' : natRank M A = natRank M s.D + 1 := by omega
  have hnAY : ¬ A ⊆ s.Y := by
    intro h
    rw [Set.union_eq_right.mpr h,s.hY.1.closure] at hAY
    exact s.hY.2.1 hAY
  exact ⟨A,⟨hA,hDA,hAr',fun h => hnAY (h.trans Set.inter_subset_right)⟩,hAW,hnAY⟩

/-- B.17: Complement [H,W,A] gives the type-(b) extension under a chosen
hyperplane H other than W. -/
theorem exists_typeB_under (s : SpecialData M Γ) {A H : Set α}
    (ha : s.TypeA A) (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y)
    (hH : IsHyperplane M H) (hAH : A ⊆ H) (hHW : H ≠ s.W) :
    ∃ B, s.TypeB B ∧ A ⊆ B ∧ B ⊆ H := by
  obtain ⟨B,hB,hAB,hBH,hBW,hBr⟩ := exists_indecomposable_complement
    (hyperplane_indecomposable hH) ha.1 s.hW.1 hAH hAW
    (hyperplane_join_eq_ground hH s.hW hHW)
  have hAr := natRank_mono (M := M) hAW
  have hBrE := natRank_mono (M := M) hB.1.subset_ground
  have hWr := hyperplane_natRank s.hW
  have hnBW : ¬ B ⊆ s.W := by
    intro h
    rw [Set.union_eq_right.mpr h,s.hW.1.closure] at hBW
    exact s.hW.2.1 hBW
  have hrA := ha.2.2.1
  exact ⟨B,⟨hB,ha.2.1.trans hAB,by omega,hnBW,fun h => hnAY (hAB.trans h)⟩,hAB,hBH⟩

/-- Identifies a constructed pole with its containing hyperplane using equal rank. -/
theorem pole_eq_of_containment {B F H : Set α} (hB : B ⊆ H) (hF : F ⊆ H)
    (hH : IsHyperplane M H) (hP : IsHyperplane M (M.closure (B ∪ F))) :
    M.closure (B ∪ F) = H := by
  have hsub := (M.closure_mono (Set.union_subset hB hF)).trans_eq hH.1.closure
  have hp := hyperplane_natRank hP
  have hh := hyperplane_natRank hH
  exact flat_eq_of_subset_of_natRank_le hP.1 hH.1 hsub (by omega)
end TutteFormalization.Homotopy.SpecialData
