import TutteFormalization.Homotopy.FirstJoinGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The hyperplane Z=L∨(K∩J) in Case 2.2. Its intersections and distinctness
are derived from the original triple, before any deformation is constructed. -/
theorem next_join_geometry {F G L H K J : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hKJ : TutteAdjacent M K J) (hF : F = H ∩ K ∩ J)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hFL : F ⊆ L) (hLH : L ⊆ H)
    (hGL : G ⊆ L) (hGK : ¬ G ⊆ K) :
    let Z := M.closure (L ∪ (K ∩ J))
    IsHyperplane M Z ∧ H ≠ Z ∧ K ≠ Z ∧ H ∩ Z = L ∧ K ∩ Z = K ∩ J ∧
      H ∩ K ∩ Z = F ∧ (Z = J ∨ TutteAdjacent M Z J) := by
  dsimp only
  let Z := M.closure (L ∪ (K ∩ J))
  have hFflat : M.IsFlat F := hF.symm ▸ flat_inter (flat_inter hH.1 hK.1) hJ.1
  have hFQ : F ⊆ K ∩ J := by rw [hF]; exact fun _ hx => ⟨hx.1.2,hx.2⟩
  have hne : L ≠ K ∩ J := fun he => hGK (hGL.trans (he ▸ Set.inter_subset_left))
  have hZ : IsHyperplane M Z := (corankThree_join_covers hFflat hrF hL hKJ.2.2 hFL hFQ hne).1
  have hLZ : L ⊆ Z := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hQZ : K ∩ J ⊆ Z := M.subset_closure_of_subset' Set.subset_union_right hKJ.2.2.1.subset_ground
  have hQH : ¬ K ∩ J ⊆ H := by
    intro hh
    have he : K ∩ J = F := Set.Subset.antisymm
      (by rw [hF]; exact fun _ hx => ⟨⟨hh hx,hx.1⟩,hx.2⟩) hFQ
    have hr := corankTwo_natRank hKJ.2.2
    rw [he] at hr
    omega
  have hHZ : H ≠ Z := fun he => hQH (hQZ.trans_eq he.symm)
  have hKZ : K ≠ Z := fun he => hGK ((hGL.trans hLZ).trans_eq he.symm)
  have hiH : H ∩ Z = L := hyperplane_inter_eq_of_corankTwo hL hH hZ hHZ hLH hLZ
  have hiK : K ∩ Z = K ∩ J := hyperplane_inter_eq_of_corankTwo hKJ.2.2 hK hZ hKZ Set.inter_subset_left hQZ
  refine ⟨hZ,hHZ,hKZ,hiH,hiK,?_,?_⟩
  · calc
      H ∩ K ∩ Z = H ∩ (K ∩ Z) := Set.inter_assoc _ _ _
      _ = H ∩ (K ∩ J) := by rw [hiK]
      _ = F := (Set.inter_assoc _ _ _).symm.trans hF.symm
  · by_cases he : Z = J
    · exact Or.inl he
    · exact Or.inr (tutteAdjacent_of_corankTwo hKJ.2.1 hKJ.2.2 hZ hJ he hQZ Set.inter_subset_right)
end TutteFormalization.Homotopy
