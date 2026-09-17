import TutteFormalization.Homotopy.ThirdCutRecognition
import TutteFormalization.Homotopy.SquarePaths

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Conditional actual-model recognition of a third-kind square. The ambient
configuration must supply four distinct covers and all spanning triples; full
cut equality and the literal labelled word are conclusions of this proof. -/
theorem third_elementary_of_four_covers (hΓ : ModularCut M Γ) {F H K J V : Set α}
    (hF : M.IsFlat F) (hrF : natRank M F + 3 = natRank M M.E)
    (P : Fin 4 → Set α) (hP : ∀ i, M.IsFlat (P i)) (hFP : ∀ i, F ⊆ P i)
    (hrP : ∀ i, natRank M (P i) = natRank M F + 1) (hinj : Function.Injective P)
    (hspan : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → M.closure ((P i ∪ P j) ∪ P k) = M.E)
    (j01 : M.closure (P 0 ∪ P 1) = H) (j02 : M.closure (P 0 ∪ P 2) = K)
    (j23 : M.closure (P 2 ∪ P 3) = J) (j13 : M.closure (P 1 ∪ P 3) = V)
    (c12 : M.closure (P 1 ∪ P 2) ∈ Γ) (c03 : M.closure (P 0 ∪ P 3) ∈ Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J) (hV : IsHyperplane M V)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hJV : TutteAdjacent M J V) (hVH : TutteAdjacent M V H)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ) (hoV : V ∉ Γ) :
    Elementary M Γ (TuttePath.square hH hK hJ hV hHK hKJ hJV hVH) := by
  obtain ⟨φ,_,hφ⟩ := exists_fourPointEmbedding hF hrF P hP hFP hrP hinj hspan
  have pair_image (i j : Fin 4) : φ.image {i,j} = M.closure (P i ∪ P j) := by
    have hc : u34.closure ({i} ∪ {j}) = {i,j} := by
      have hh : ∀ i j : Fin 4, u34.closure ({i} ∪ {j}) = {i,j} := by decide
      exact hh i j
    simpa only [hc,hφ] using φ.map_join {i} {j} (u34_simple.2 i).1 (u34_simple.2 j).1
  have im01 := (pair_image 0 1).trans j01
  have im02 := (pair_image 0 2).trans j02
  have im23 := (pair_image 2 3).trans j23
  have im13 := (pair_image 1 3).trans j13
  have cut := exact_thirdCut φ hΓ
    (by rw [pair_image]; exact Or.inl c12) (by rw [pair_image]; exact Or.inl c03)
    (by rw [im01]; exact (hyperplane_off_cutPlus hH).mpr hoH)
    (by rw [im02]; exact (hyperplane_off_cutPlus hK).mpr hoK)
    (by rw [im23]; exact (hyperplane_off_cutPlus hJ).mpr hoJ)
    (by rw [im13]; exact (hyperplane_off_cutPlus hV).mpr hoV)
  refine Elementary.base (BaseElementary.third φ _ cut ?_ rfl
    ((off_cutPlus _).mpr (TuttePath.square_off hH hK hJ hV hHK hKJ hJV hVH hoH hoK hoJ hoV)))
  rw [TuttePath.square_word]
  simp only [List.map_cons,List.map_nil,im01,im02,im23,im13]
end TutteFormalization.Homotopy
