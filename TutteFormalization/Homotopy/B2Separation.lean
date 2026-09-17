import TutteFormalization.Homotopy.SeparationSides

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- The repaired last paragraph of B.2. Local uniqueness below X and Y first
identifies the constructed opposite-side hyperplane with Y, then forces Q=L.
The uniqueness premises are discharged by the earlier minimality argument. -/
theorem flat_eq_of_unique_decomposable_intersections {Q L X Y : Set α}
    (hQ : M.IsFlat Q) (hnQ : ¬ Indecomposable M Q) (hQL : Q ⊆ L)
    (hL : CorankTwo M L) (hnL : ¬ Indecomposable M L)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hLX : L ⊆ X) (hLY : L ⊆ Y)
    (uniqueX : ∀ I, CorankTwo M I → ¬ Indecomposable M I → Q ⊆ I → I ⊆ X → I = L)
    (uniqueY : ∀ I, CorankTwo M I → ¬ Indecomposable M I → Q ⊆ I → I ⊆ Y → I = L) :
    Q = L := by
  have hQX := hQL.trans hLX
  have hQY := hQL.trans hLY
  have hI := hyperplane_inter_eq_of_corankTwo hL hX hY hXY hLX hLY
  have htwo : ∀ H, IsHyperplane M H → L ⊆ H → H = X ∨ H = Y := by
    intro H hH hLH
    exact (separation_hyperplanes hX hY (by simpa only [hI] using hnL)).2 H hH
      (by simpa only [hI] using hLH)
  obtain ⟨A,B,K,hd,hA,hB,hu,hr,hAX,hK,hQK,hBK,hXK,hnXK,hcXK⟩ :=
    exists_opposite_separation_hyperplane hQ hnQ hX hQX
  have hXKL : X ∩ K = L := uniqueX _ hcXK hnXK (Set.subset_inter hQX hQK)
    Set.inter_subset_left
  have hLK : L ⊆ K := hXKL ▸ Set.inter_subset_right
  have hKY : K = Y := (htwo K hK hLK).resolve_left (fun h => hXK h.symm)
  have hBY : B ⊆ Y \ Q := by simpa only [hKY] using hBK
  have oppNe {H K : Set α} (hH : IsHyperplane M H) (hQH : Q ⊆ H)
      (hAH : A ⊆ H \ Q) (hBK : B ⊆ K \ Q) : H ≠ K := by
    intro heq
    have hN := hyperplane_sdiff_contract hQ hH hQH
    apply hN.2.1
    apply Set.Subset.antisymm hN.1.subset_ground
    rw [← hu]
    exact Set.union_subset hAH (by simpa only [← heq] using hBK)
  have all : ∀ H, IsHyperplane M H → Q ⊆ H → H = X ∨ H = Y := by
    intro H hH hQH
    rcases hyperplane_contains_partition_side hd hu hr
      (hyperplane_sdiff_contract hQ hH hQH) with hAH | hBH
    · have hHY : H ≠ Y := oppNe hH hQH hAH hBY
      have hn := opposite_contract_hyperplanes_decomposable hQ hd hu hr
        hH hY hQH hQY hAH hBY
      have hc := decomposable_inter_corankTwo hH hY hHY hn
      have heq := uniqueY _ hc hn (Set.subset_inter hQH hQY) Set.inter_subset_right
      exact htwo H hH (heq ▸ Set.inter_subset_left)
    · have hXH : X ≠ H := oppNe hX hQX hAX hBH
      have hn := opposite_contract_hyperplanes_decomposable hQ hd hu hr
        hX hH hQX hQH hAX hBH
      have hc := decomposable_inter_corankTwo hX hH hXH hn
      have heq := uniqueX _ hc hn (Set.subset_inter hQX hQH) Set.inter_subset_left
      exact htwo H hH (heq ▸ Set.inter_subset_right)
  apply Set.Subset.antisymm hQL
  apply subset_flat_of_forall_hyperplane hQ hL.1.subset_ground
  intro H hH hQH
  rcases all H hH hQH with rfl | rfl
  · exact hLX
  · exact hLY
end TutteFormalization.Homotopy
