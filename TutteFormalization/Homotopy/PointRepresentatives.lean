import TutteFormalization.Homotopy.ContractGeometry
import TutteFormalization.RelativeComplement

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- A covering flat has an actual ground-element representative after
contraction by its bottom. This supplies labels, not a new abstract model. -/
theorem exists_contracted_point {D P : Set α} (hD : M.IsFlat D) (hP : M.IsFlat P)
    (hDP : D ⊆ P) (hrP : natRank M P = natRank M D + 1) :
    ∃ e, e ∈ P \ D ∧ (M ／ D).closure {e} = P \ D := by
  have hn : ¬ P ⊆ D := by
    intro h
    have := natRank_mono (M := M) h
    omega
  obtain ⟨e,heP,heD⟩ := Set.not_subset.mp hn
  have hsub : M.closure (insert e D) ⊆ P :=
    (M.closure_mono (Set.insert_subset heP hDP)).trans_eq hP.closure
  have hr := natRank_closure_insert hD (hP.subset_ground heP) heD
  have heq := flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) hP hsub (by omega)
  refine ⟨e,⟨heP,heD⟩,?_⟩
  rw [M.contract_closure_eq,Set.singleton_union,heq]

/-- Representative incidence is exactly flat incidence above the contracted
bottom. This turns geometric subset data into the finite labelled model table. -/
theorem contracted_point_mem_iff {D P H : Set α} {e : α}
    (hP : M.IsFlat P) (hH : M.IsFlat H) (hDP : D ⊆ P) (hDH : D ⊆ H)
    (heP : e ∈ P \ D) (he : (M ／ D).closure {e} = P \ D) :
    e ∈ H \ D ↔ P ⊆ H := by
  constructor
  · intro heH
    have hsub : (M ／ D).closure {e} ⊆ H \ D :=
      ((M ／ D).closure_mono (Set.singleton_subset_iff.mpr heH)).trans_eq
        (flat_sdiff_contract hH hDH).closure
    rw [he] at hsub
    intro x hx
    by_cases hxD : x ∈ D
    · exact hDH hxD
    · exact (hsub ⟨hx,hxD⟩).1
  · intro h; exact ⟨h heP.1,heP.2⟩

/-- Distinct covering flats have distinct representative labels. -/
theorem contracted_representatives_injective {ι : Type*} {D : Set α}
    (P : ι → Set α) (hDP : ∀ i, D ⊆ P i) (hinj : Function.Injective P)
    (e : ι → α) (he : ∀ i, (M ／ D).closure {e i} = P i \ D) : Function.Injective e := by
  intro i j hij
  apply hinj
  have hh := (he i).symm.trans ((congrArg (fun x => (M ／ D).closure {x}) hij).trans (he j))
  have hu := congrArg (fun S => S ∪ D) hh
  simpa only [Set.sdiff_union_of_subset (hDP i),Set.sdiff_union_of_subset (hDP j)] using hu
end TutteFormalization.Homotopy
