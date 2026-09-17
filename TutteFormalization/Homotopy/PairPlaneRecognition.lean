import TutteFormalization.Homotopy.FourthRankRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

def labelPair (i : Fin 3) : Finset (Fin 6) := {⟨i.val,by omega⟩,⟨i.val+3,by omega⟩}

set_option maxRecDepth 100000 in
-- This is precisely the (2,1,1) distribution among the three labelled pairs.
theorem four_nonCircuit_pair : ∀ B : Finset (Fin 6), B.card = 4 → B ∉ fourCircuits →
    (∃ i, labelPair i ⊆ B) ∧ (∀ j : Fin 3, ∃ k ∈ B, k.val % 3 = j.val) := by decide

set_option maxRecDepth 100000 in
theorem circuit_missing_pair : ∀ C ∈ fourCircuits, C.card = 4 ∧
    ∃ j : Fin 3, ∀ k ∈ C, k.val % 3 ≠ j.val := by decide

variable (e : Fin 6 → α) (he : ∀ i, e i ∈ M.E) (hinj : Function.Injective e)
    (planes : Fin 3 → Set α) (hplanes : ∀ j, IsHyperplane M (planes j))
    (incidence : ∀ (k : Fin 6) (j : Fin 3), e k ∈ planes j ↔ k.val % 3 ≠ j.val)
    (hpair : ∀ i, CorankTwo M (M.closure (e '' (labelPair i : Set (Fin 6)))))
    (hdec : ∀ i, ¬ Indecomposable M (M.closure (e '' (labelPair i : Set (Fin 6)))))
    (hM : natRank M M.E = 4)

include he hplanes incidence hpair hdec in
/-- The rank-four spanning argument from the recognition supplement, using
B.1 on a complete decomposable pair and the two opposite missing-pair planes. -/
theorem nonCircuit_four_spans (B : Finset (Fin 6)) (hB : B.card = 4)
    (hnB : B ∉ fourCircuits) : M.closure (e '' (B : Set (Fin 6))) = M.E := by
  obtain ⟨⟨i,hiB⟩,hall⟩ := four_nonCircuit_pair B hB hnB
  have others : ∀ i : Fin 3, ∃ j k : Fin 3, j ≠ k ∧ i ≠ j ∧ i ≠ k := by decide
  obtain ⟨j,k,hjk,hij,hik⟩ := others i
  have pair_sub : ∀ t : Fin 3, i ≠ t →
      M.closure (e '' (labelPair i : Set (Fin 6))) ⊆ planes t := by
    intro t hit
    apply (M.closure_mono ?_).trans_eq (hplanes t).1.closure
    rintro _ ⟨a,ha,rfl⟩
    apply (incidence a t).mpr
    have hai : a.val % 3 = i.val := by
      simp only [labelPair,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp <;> omega
    intro hh
    exact hit (Fin.ext (hai.symm.trans hh))
  have hne : planes j ≠ planes k := by
    let a : Fin 6 := ⟨j.val,by omega⟩
    have hm : a.val % 3 = j.val := Nat.mod_eq_of_lt j.isLt
    have haK : e a ∈ planes k := (incidence a k).mpr (by
      rw [hm]; exact fun h => hjk (Fin.ext h))
    have haJ : e a ∉ planes j := fun h => (incidence a j).mp h hm
    intro h
    exact haJ (h ▸ haK)
  apply spans_of_decomposable_pair (hpair i) (hdec i) (hplanes j) (hplanes k)
    hne (pair_sub j hij) (pair_sub k hik)
    (by rintro _ ⟨a,_,rfl⟩; exact he a) (M.closure_mono (Set.image_mono hiB))
  · intro h
    obtain ⟨a,ha,hr⟩ := hall j
    exact (incidence a j).mp (h ⟨a,ha,rfl⟩) hr
  · intro h
    obtain ⟨a,ha,hr⟩ := hall k
    exact (incidence a k).mp (h ⟨a,ha,rfl⟩) hr

include he hinj hplanes incidence hpair hdec hM in
theorem nonCircuit_four_indep (B : Finset (Fin 6)) (hB : B.card = 4)
    (hnB : B ∉ fourCircuits) : M.Indep (e '' (B : Set (Fin 6))) := by
  have hspan := nonCircuit_four_spans e he planes hplanes incidence hpair hdec B hB hnB
  apply M.indep_iff_eRk_eq_encard.mpr
  rw [← M.eRk_closure_eq, hspan, ← cast_natRank M M.E,hM]
  rw [hinj.encard_image]
  simp [hB]

include he hinj hplanes incidence hpair hdec hM in
theorem pair_plane_circuit_rank (C : Finset (Fin 6)) (hC : C ∈ fourCircuits) :
    natRank M (e '' (C : Set (Fin 6))) = 3 := by
  obtain ⟨hcard,j,hj⟩ := circuit_missing_pair C hC
  have hsub : e '' (C : Set (Fin 6)) ⊆ planes j := by
    rintro _ ⟨a,ha,rfl⟩
    exact (incidence a j).mpr (hj a ha)
  have hu := natRank_mono (M := M) hsub
  have hpr := hyperplane_natRank (hplanes j)
  obtain ⟨T,hTC,hTr⟩ := Finset.exists_subset_card_eq (show 3 ≤ C.card by omega)
  obtain ⟨B,hTB,hBc,hBn⟩ := bipartite_small_extension T (by omega)
  have hind := (nonCircuit_four_indep e he hinj planes hplanes incidence hpair hdec hM B hBc hBn).subset
    (Set.image_mono (f := e) (show (T : Set (Fin 6)) ⊆ B from hTB))
  have hr := natRank_eq_ncard_of_isBasis hind.isBasis_self
  rw [Set.ncard_image_of_injective _ hinj] at hr
  simp only [Set.ncard_coe_finset,hTr] at hr
  have hl := natRank_mono (M := M) (Set.image_mono (f := e) (show (T : Set (Fin 6)) ⊆ C from hTC))
  omega

/-- Actual ambient model recognition from three decomposable pair flats and
verified incidences of their three containing planes. No model is assumed. -/
noncomputable def fourthModelOfPairPlanes : ModelEmbedding bipartiteModel M :=
  fourthModelOfBases e he hinj hM
    (nonCircuit_four_indep e he hinj planes hplanes incidence hpair hdec hM)
    (pair_plane_circuit_rank e he hinj planes hplanes incidence hpair hdec hM)
end TutteFormalization.Homotopy
