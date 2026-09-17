import TutteFormalization.Homotopy.OffJoinReduction

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The Diamond choice L' in Case 2.2.2, distinct from the incoming
edge intersection. The excluded set need not satisfy any extra hypothesis. -/
theorem exists_other_corankTwo {F J Q : Set α} (hF : Indecomposable M F)
    (hrF : natRank M F + 3 = natRank M M.E) (hJ : IsHyperplane M J) (hFJ : F ⊆ J) :
    ∃ P, Indecomposable M P ∧ CorankTwo M P ∧ F ⊆ P ∧ P ⊆ J ∧ P ≠ Q := by
  have hrJ := hyperplane_natRank hJ
  obtain ⟨V,W,hV,hW,hFV,hFW,hVJ,hWJ,hVW,hrV,hrW⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hJ) hF hFJ (by omega)
  by_cases he : V = Q
  · exact ⟨W,hW,(corankTwo_iff_natRank hW.1).mpr (by omega),hFW,hWJ,
      fun hh => hVW (he.trans hh.symm)⟩
  · exact ⟨V,hV,(corankTwo_iff_natRank hV.1).mpr (by omega),hFV,hVJ,he⟩

/-- The preliminary subcase of 2.2.2: if the chosen L' is below H,
the actual corank-three triangle shortens the path. -/
theorem corankThree_triangle_shortcut_decreases (hΓ : ModularCut M Γ) {H K J P D G : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hrF : natRank M (H ∩ K ∩ J) + 3 = natRank M M.E)
    (hP : Indecomposable M P) (hcP : CorankTwo M P) (hPH : P ⊆ H) (hPJ : P ⊆ J)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ)
    (hDH : D ⊆ H) (hDJ : D ⊆ J) (hGK : ¬ G ⊆ K) :
    ∃ q : TuttePath M,
      Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) q ∧
      q.On D ∧ outsideCount q G <
        outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) G := by
  have hHJ : H ≠ J := by
    intro he
    have hi : H ∩ K ∩ J = H ∩ K := by rw [← he]; exact Set.inter_eq_left.mpr Set.inter_subset_left
    have hr := corankTwo_natRank hHK.2.2
    rw [hi] at hrF
    omega
  have hHJadj := tutteAdjacent_of_corankTwo hP hcP hH hJ hHJ hPH hPJ
  refine ⟨TuttePath.edge hH hJ hHJadj,?_,TuttePath.edge_on _ _ _ hDH hDJ,?_⟩
  · exact triangle_shortcut hΓ hH hK hJ hHK hKJ hHJadj.symm
      (elementary_null (triangle_rankThree_elementary hΓ hH hK hJ hHK hKJ hHJadj.symm hrF hoH hoK hoJ))
  · classical
    rw [outsideCount_word,outsideCount_word]
    change [H,J].countP _ < [H,K,J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [hGK,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
end TutteFormalization.Homotopy
