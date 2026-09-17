import TutteFormalization.Homotopy.PointGeneration
import TutteFormalization.Homotopy.RankTableEmbedding

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}

/-- Every ambient hyperplane is represented if all indecomposable points are
represented. This uses Chain/Diamond generation; it does not assert that every
ambient flat belongs to the selected lattice. -/
theorem hyperplane_generated_by_labels (e : Fin n → α) (he : ∀ i, e i ∈ M.E)
    (hr : ∀ S : Finset (Fin n), natRank M (e '' (S : Set (Fin n))) = N.rank S)
    (h0 : Indecomposable M ∅)
    (points : ∀ P, Indecomposable M P → natRank M P = 1 →
      ∃ i, P = M.closure {e i})
    {H : Set α} (hH : IsHyperplane M H) :
    ∃ F : Finset (Fin n), N.Flat F ∧ M.closure (e '' (F : Set (Fin n))) = H := by
  classical
  let F : Finset (Fin n) := Finset.univ.filter (fun i => e i ∈ H)
  have hFH : e '' (F : Set (Fin n)) ⊆ H := by
    rintro _ ⟨i,hi,rfl⟩
    exact (Finset.mem_filter.mp hi).2
  have hKH : M.closure (e '' (F : Set (Fin n))) ⊆ H :=
    (M.closure_mono hFH).trans_eq hH.1.closure
  have hHK : H ⊆ M.closure (e '' (F : Set (Fin n))) := by
    apply indecomposable_subset_of_covers_subset h0 (hyperplane_indecomposable hH)
      (Set.empty_subset _) (M.isFlat_closure _) (Set.empty_subset _)
    intro P hP h0P hPH hPr
    have hrP : natRank M P = 1 := by simpa [natRank] using hPr
    obtain ⟨i,rfl⟩ := points P hP hrP
    have hei : e i ∈ H := hPH (M.subset_closure _ (Set.singleton_subset_iff.mpr (he i)) rfl)
    apply M.closure_mono
    rintro a rfl
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hei⟩,rfl⟩
  have hEq := Set.Subset.antisymm hKH hHK
  refine ⟨F,?_,hEq⟩
  apply Finset.ext
  intro i
  rw [← ModelEmbedding.label_mem_closure_iff e he hr F i,hEq]
  simp [F]

/-- In rank four the selected hyperplanes are exactly the eleven graphic
hyperplanes; additional decomposable ambient points are not excluded. -/
theorem fourth_hyperplanes_recognized (e : Fin 6 → α) (he : ∀ i, e i ∈ M.E)
    (hr : ∀ S : Finset (Fin 6), natRank M (e '' (S : Set (Fin 6))) = bipartiteModel.rank S)
    (h0 : Indecomposable M ∅) (hM : natRank M M.E = 4)
    (points : ∀ P, Indecomposable M P → natRank M P = 1 → ∃ i, P = M.closure {e i})
    {H : Set α} (hH : IsHyperplane M H) :
    ∃ F ∈ bipartiteHyperplanes, M.closure (e '' (F : Set (Fin 6))) = H := by
  obtain ⟨F,hF,hFH⟩ := hyperplane_generated_by_labels e he hr h0 points hH
  have hFr : bipartiteModel.rank F = 3 := by
    have h := hyperplane_natRank hH
    rw [← hFH,natRank_closure,hr] at h
    omega
  have hfinite : ∀ F, bipartiteModel.Flat F → bipartiteModel.rank F = 3 →
      F ∈ bipartiteHyperplanes := by decide
  exact ⟨F,hfinite F hF hFr,hFH⟩
end TutteFormalization.Homotopy
