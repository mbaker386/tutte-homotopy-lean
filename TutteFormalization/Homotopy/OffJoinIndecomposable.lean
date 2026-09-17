import TutteFormalization.Homotopy.NextJoinGeometry
import TutteFormalization.Homotopy.TriangleExchange

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.1 when L is indecomposable: replace H,K,J by H,Z,J (or H,Z
when Z=J), with the actual triangle homotopies and strict occurrence decrease. -/
theorem off_join_indec_shortcut (hΓ : ModularCut M Γ) {D F G L H K J : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hF : F = H ∩ K ∩ J) (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hiL : Indecomposable M L) (hFL : F ⊆ L) (hLH : L ⊆ H)
    (hGL : G ⊆ L) (hGK : ¬ G ⊆ K) (hDG : D ⊆ G) (hDJ : D ⊆ J)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ)
    (hoZ : M.closure (L ∪ (K ∩ J)) ∉ Γ) :
    ∃ q : TuttePath M,
      Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) q ∧
      q.On D ∧ outsideCount q G <
        outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) G := by
  let Z := M.closure (L ∪ (K ∩ J))
  obtain ⟨hZ,hHZne,hKZne,hHZeq,hKZeq,htriple,_⟩ :=
    next_join_geometry hH hK hJ hKJ hF hrF hL hFL hLH hGL hGK
  have hLZ : L ⊆ Z := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hQZ : K ∩ J ⊆ Z := M.subset_closure_of_subset' Set.subset_union_right hKJ.2.2.1.subset_ground
  have hHZ : TutteAdjacent M H Z := tutteAdjacent_of_corankTwo hiL hL hH hZ hHZne hLH hLZ
  have hKZ : TutteAdjacent M K Z := tutteAdjacent_of_corankTwo hKJ.2.1 hKJ.2.2 hK hZ hKZne
    Set.inter_subset_left hQZ
  have hGZ : G ⊆ Z := hGL.trans hLZ
  have hGH : G ⊆ H := hGL.trans hLH
  have h1 := triangle_shortcut hΓ hH hK hZ hHK hKZ hHZ.symm
    (elementary_null (triangle_rankThree_elementary hΓ hH hK hZ hHK hKZ hHZ.symm
      (by simpa only [htriple] using hrF) hoH hoK hoZ))
  by_cases he : Z = J
  · have hed : (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl =
        (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl := by
      apply TuttePath.eq_of_word_eq
      change [H,K,J] = [H,K,Z]
      exact congrArg (fun A => [H,K,A]) he.symm
    refine ⟨TuttePath.edge hH hZ hHZ,?_,TuttePath.edge_on _ _ _ (hDG.trans hGH) (hDG.trans hGZ),?_⟩
    · rw [hed]; exact h1
    · classical
      rw [outsideCount_word,outsideCount_word]
      change [H,Z].countP (fun A => decide (¬ G ⊆ A)) < [H,K,J].countP (fun A => decide (¬ G ⊆ A))
      have hGJ := hGZ.trans_eq he
      simp [hGH,hGZ,hGK,hGJ]
  · have hZJ := tutteAdjacent_of_corankTwo hKJ.2.1 hKJ.2.2 hZ hJ he hQZ Set.inter_subset_right
    have h2 := triangle_shortcut hΓ hK hZ hJ hKZ hZJ hKJ.symm
      (elementary_null (triangle_rankTwo_elementary hΓ hKJ.2.2 hK hZ hJ hKZ hZJ hKJ.symm
        Set.inter_subset_left hQZ Set.inter_subset_right hoK hoZ hoJ))
    refine ⟨(TuttePath.edge hH hZ hHZ).concat (TuttePath.edge hZ hJ hZJ) rfl,
      triangle_exchange hH hK hJ hZ hHK hKJ hHZ hKZ hZJ h1 h2,?_,
      twoEdge_count_decreases hH hK hJ hZ hHK hKJ hHZ hZJ hGZ hGK⟩
    exact TuttePath.concat_on (TuttePath.edge_on _ _ _ (hDG.trans hGH) (hDG.trans hGZ))
      (TuttePath.edge_on _ _ _ (hDG.trans hGZ) hDJ) rfl
end TutteFormalization.Homotopy
