import TutteFormalization.Homotopy.OffJoinSpecial
import TutteFormalization.Homotopy.SquareShortcut

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.1 when L is decomposable. The auxiliary square is filled by
Lower or Special, and the remaining corank-two triangle supplies the tail. -/
theorem off_join_decomp_shortcut (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) {D F G L H K J : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hiF : Indecomposable M F) (hF : F = H ∩ K ∩ J)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L) (hFL : F ⊆ L) (hLH : L ⊆ H)
    (hiG : Indecomposable M G) (hGL : G ⊆ L) (hGK : ¬ G ⊆ K)
    (hDG : D ⊆ G) (hDF : D ⊆ F) (hrD : natRank M M.E - natRank M D ≤ n+1)
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
  have hKZ : TutteAdjacent M K Z := tutteAdjacent_of_corankTwo hKJ.2.1 hKJ.2.2 hK hZ hKZne
    Set.inter_subset_left hQZ
  have hGZ : G ⊆ Z := hGL.trans hLZ
  have hGH : G ⊆ H := hGL.trans hLH
  obtain ⟨T,hT,hTH,hTZ,hoT,hGT,hn⟩ := exists_off_special_bridge hM hΓ hlower
    hH hK hZ hHK hKZ hoH hoK hoZ hiF htriple hrF hiG hL hnL hHZeq hHZne
    hGL hGK hDG hDF hrD
  let b := (TuttePath.edge hH hT hTH.symm).concat (TuttePath.edge hT hZ hTZ) rfl
  have h1 : Homotopic M Γ
      ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl) b :=
    square_shortcut hΓ hH hK hZ hT hHK hKZ hTZ.symm hTH hn
  have hbD : b.On D := TuttePath.concat_on
    (TuttePath.edge_on _ _ _ (hDG.trans hGH) (hDG.trans hGT))
    (TuttePath.edge_on _ _ _ (hDG.trans hGT) (hDG.trans hGZ)) rfl
  have htword : ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl).word = [H,K,J] := rfl
  by_cases he : Z = J
  · have hed : (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl =
        (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl := by
      apply TuttePath.eq_of_word_eq
      change [H,K,J] = [H,K,Z]
      exact congrArg (fun A => [H,K,A]) he.symm
    refine ⟨b,hed.symm ▸ h1,hbD,?_⟩
    classical
    rw [outsideCount_word,outsideCount_word,htword]
    change [H,T,Z].countP _ < _
    have hGJ := hGZ.trans_eq he
    simp only [List.countP_cons,List.countP_nil]
    simp [hGH,hGT,hGZ,hGK,hGJ]
  · have hZJ := tutteAdjacent_of_corankTwo hKJ.2.1 hKJ.2.2 hZ hJ he hQZ Set.inter_subset_right
    let e := TuttePath.edge hZ hJ hZJ
    have h2 := triangle_shortcut hΓ hK hZ hJ hKZ hZJ hKJ.symm
      (elementary_null (triangle_rankTwo_elementary hΓ hKJ.2.2 hK hZ hJ hKZ hZJ hKJ.symm
        Set.inter_subset_left hQZ Set.inter_subset_right hoK hoZ hoJ))
    have ha := h2.symm.prepend (TuttePath.edge hH hK hHK)
      ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ hoH hoK)) rfl
    have hb := h1.append e ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ hoZ hoJ)) rfl
    have hassoc := TuttePath.concat_assoc (TuttePath.edge hH hK hHK)
      (TuttePath.edge hK hZ hKZ) e rfl rfl
    have hcomp : Homotopic M Γ
        ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) (b.concat e rfl) :=
      ha.trans (hassoc ▸ hb)
    have hDJ : D ⊆ J := hDF.trans (hF ▸ Set.inter_subset_right)
    refine ⟨b.concat e rfl,hcomp,TuttePath.concat_on hbD
      (TuttePath.edge_on _ _ _ (hDG.trans hGZ) hDJ) rfl,?_⟩
    classical
    rw [outsideCount_word,outsideCount_word,htword]
    change [H,T,Z,J].countP _ < _
    simp only [List.countP_cons,List.countP_nil]
    simp [hGH,hGT,hGZ,hGK]
end TutteFormalization.Homotopy
