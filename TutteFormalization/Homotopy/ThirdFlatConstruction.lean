import TutteFormalization.Homotopy.SpecialData
import TutteFormalization.Homotopy.ThirdFlatGeometry

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.23's two Complement applications and construction F₃=G∨G″. The
F₂∨I=E premise is supplied by the checked HD-008 argument in B.22. -/
theorem exists_third_flat (s : SpecialData M Γ) {G I : Set α}
    (hG : Indecomposable M G) (hDG : s.D ⊆ G) (hGF : G ⊆ s.F₁)
    (hrG : natRank M G + 4 = natRank M M.E) (hI : IsHyperplane M I) (hGI : G ⊆ I)
    (hdW : ¬ Indecomposable M (s.W ∩ I)) (hdY : ¬ Indecomposable M (s.Y ∩ I))
    (hj₁ : M.closure (s.F₁ ∪ I) = M.E) (hj₂ : M.closure (s.F₂ ∪ I) = M.E) :
    ∃ K Q, Indecomposable M K ∧ s.D ⊆ K ∧ K ⊆ s.F₂ ∧
      natRank M K = natRank M s.D + 1 ∧ Indecomposable M Q ∧
      G ⊆ Q ∧ K ⊆ Q ∧ Q ⊆ s.W ∩ s.Y ∧ natRank M Q + 3 = natRank M M.E := by
  obtain ⟨K,hK,hDK,hKF,hKI,hKr⟩ := exists_indecomposable_complement s.second_indec s.D_indec
    hI.1 s.D_subset_second (hDG.trans hGI) hj₂
  have hrI := hyperplane_natRank hI
  have hDr := natRank_mono (M := M) (hDG.trans hGI)
  have hKrE := natRank_mono (M := M) hK.1.subset_ground
  have hKr' : natRank M K = natRank M s.D + 1 := by omega
  have hnKI : ¬ K ⊆ I := by
    intro h
    rw [Set.union_eq_right.mpr h,hI.1.closure] at hKI
    exact hI.2.1 hKI
  let Q := M.closure (G ∪ K)
  have hQ : M.IsFlat Q := M.isFlat_closure _
  have hGQ : G ⊆ Q := M.subset_closure_of_subset' Set.subset_union_left hG.1.subset_ground
  have hKQ : K ⊆ Q := M.subset_closure_of_subset' Set.subset_union_right hK.1.subset_ground
  have hnQI : ¬ Q ⊆ I := fun h => hnKI (hKQ.trans h)
  have hnGQ : G ≠ Q := fun h => hnQI (h.symm.subset.trans hGI)
  have hlo := natRank_lt_of_flat_ssubset hG.1 hQ (Set.ssubset_iff_subset_ne.mpr ⟨hGQ,hnGQ⟩)
  have hu := natRank_submodular M G K
  have hm := natRank_mono (M := M) (Set.subset_inter hDG hDK)
  have hrQ : natRank M Q + 3 = natRank M M.E := by
    change _ + natRank M Q ≤ _ at hu
    omega
  have hGm : G ⊆ s.W ∩ s.Y := hGF.trans (fun _ h => ⟨h.1.1,h.2⟩)
  have hKm : K ⊆ s.W ∩ s.Y := hKF.trans (fun _ h => ⟨h.2,h.1.1⟩)
  have hQm : Q ⊆ s.W ∩ s.Y := (M.closure_mono (Set.union_subset hGm hKm)).trans_eq s.middle_corank.1.closure
  have hnLmI : ¬ s.W ∩ s.Y ⊆ I := by
    intro h
    rcases (separation_hyperplanes s.hW s.hY s.middle_decomp).2 I hI h with hi | hi
    · subst I; exact hdW (by simpa using hyperplane_indecomposable s.hW)
    · subst I; exact hdY (by simpa using hyperplane_indecomposable s.hY)
  have hjIm : M.closure (I ∪ (s.W ∩ s.Y)) = M.E := by
    have hIJ : I ⊆ M.closure (I ∪ (s.W ∩ s.Y)) :=
      M.subset_closure_of_subset' Set.subset_union_left hI.1.subset_ground
    have hLJ : s.W ∩ s.Y ⊆ M.closure (I ∪ (s.W ∩ s.Y)) :=
      M.subset_closure_of_subset' Set.subset_union_right s.middle_corank.1.subset_ground
    rcases hI.2.2 _ (M.isFlat_closure _) hIJ with heq | heq
    · exact False.elim (hnLmI (hLJ.trans_eq heq))
    · exact heq
  obtain ⟨L,hL,hGL,hLI,hjoin,hLr⟩ := exists_indecomposable_complement
    (hyperplane_indecomposable hI) hG s.middle_corank.1 hGI hGm hjIm
  have hmr := corankTwo_natRank s.middle_corank
  have hLrE := natRank_mono (M := M) hL.1.subset_ground
  have hcL : CorankTwo M L := (corankTwo_iff_natRank hL.1).mpr (by omega)
  have hnPI : ¬ s.F₁ ⊆ I := by
    intro h
    rw [Set.union_eq_right.mpr h,hI.1.closure] at hj₁
    exact hI.2.1 hj₁
  have hQind := third_flat_indecomposable s.hW s.hY hI s.W_ne_Y s.middle_corank
    s.middle_decomp hdW hdY hG.1 hrG s.first_indec s.first_rank hGF
    (fun _ h => ⟨h.1.1,h.2⟩) hQ hrQ hGQ hQm hcL hGL hLI hjoin hnPI hnQI
  exact ⟨K,Q,hK,hDK,hKF,hKr',hQind,hGQ,hKQ,hQm,hrQ⟩
end TutteFormalization.Homotopy.SpecialData
