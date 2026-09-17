import TutteFormalization.Homotopy.SixModelCubes

namespace TutteFormalization.Homotopy.SixFlatData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

theorem plane_image_eq {F : Finset (Fin 6)} (hF : F ∈ bipartiteHyperplanes) (j : Fin 3)
    (hinc : ∀ i ∈ F, i.val % 3 ≠ j.val) : d.ambientModel.image F = c.planes j := by
  have hsub : d.ambientModel.image F ⊆ c.planes j := by
    rw [d.ambientModel_image]
    apply (M.closure_mono (Set.union_subset ?_ (c.planes_above j))).trans_eq (c.planes_hyperplane j).1.closure
    rintro _ ⟨i,hi,rfl⟩
    exact ((d.representative_incidence i j).mpr (hinc i hi)).1
  exact flat_eq_of_subset_of_natRank_le (d.model_hyperplane hF).1 (c.planes_hyperplane j).1 hsub
    (by have := hyperplane_natRank (d.model_hyperplane hF)
        have := hyperplane_natRank (c.planes_hyperplane j); omega)

theorem first_plane_image : d.ambientModel.image {0,1,3,4} = s.W :=
  d.plane_image_eq (by decide) 2 (by decide)

theorem second_plane_image : d.ambientModel.image {0,2,3,5} = s.Y :=
  d.plane_image_eq (by decide) 1 (by decide)

/-- A hyperplane above D distinct from all three pair-planes is a cube triple. -/
theorem other_hyperplane_cube {H : Set α} (hH : IsHyperplane M H) (hDH : s.D ⊆ H)
    (hne : ∀ j, H ≠ c.planes j) : ∃ i, d.ambientModel.image (cubeTriple i) = H := by
  obtain ⟨F,hF,he⟩ := d.hyperplanes_recognized hH hDH
  have cases : ∀ F ∈ bipartiteHyperplanes, F ∈ fourCircuits ∨ ∃ i, cubeTriple i = F := by decide
  rcases cases F hF with hc | ⟨i,hi⟩
  · obtain ⟨j,hj⟩ := d.circuit_plane hc
    exact False.elim (hne j (he.symm.trans hj))
  · exact ⟨i,hi.symm ▸ he⟩

/-- Recognition of the original ordered path, including the opposite labels
0 and 3 determined by its two original special flats. -/
theorem original_path_word : ∃ x y : Fin 8, x.val % 2 ≠ y.val % 2 ∧
    s.path.word = [{0,1,3,4},cubeTriple x,{0,2,3,5},cubeTriple y,{0,1,3,4}].map d.ambientModel.image := by
  have hF₁X : s.F₁ ⊆ s.X := fun _ h => h.1.2
  have hF₂Z : s.F₂ ⊆ s.Z := fun _ h => h.1.2
  have hnX : ∀ j, s.X ≠ c.planes j := by
    intro j; fin_cases j
    · exact fun he => c.first_not_below_T (hF₁X.trans_eq he)
    · exact s.hXY.1
    · exact s.hWX.1.symm
  have hnZ : ∀ j, s.Z ≠ c.planes j := by
    intro j; fin_cases j
    · exact fun he => c.second_not_below_T (hF₂Z.trans_eq he)
    · exact s.hYZ.1.symm
    · exact s.hZW.1
  obtain ⟨x,hx⟩ := d.other_hyperplane_cube s.hX (s.D_subset_first.trans hF₁X) hnX
  obtain ⟨y,hy⟩ := d.other_hyperplane_cube s.hZ (s.D_subset_second.trans hF₂Z) hnZ
  have h0 : (0 : Fin 6) ∈ cubeTriple x := (d.point_below_cube_iff 0 x).mp (by rw [d.first,hx]; exact hF₁X)
  have h3 : (3 : Fin 6) ∈ cubeTriple y := (d.point_below_cube_iff 3 y).mp (by rw [d.second,hy]; exact hF₂Z)
  have hbits : ∀ i : Fin 8, (0 ∈ cubeTriple i → i.val % 2 = 0) ∧
      (3 ∈ cubeTriple i → i.val % 2 = 1) := by decide
  refine ⟨x,y,by have := (hbits x).1 h0; have := (hbits y).2 h3; omega,?_⟩
  change (TuttePath.square s.hW s.hX s.hY s.hZ s.hWX s.hXY s.hYZ s.hZW).word = _
  rw [TuttePath.square_word]
  simp only [List.map_cons,List.map_nil,d.first_plane_image,d.second_plane_image,hx,hy]
end TutteFormalization.Homotopy.SixFlatData
