import TutteFormalization.Homotopy.Special

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Distinct special triple flats force carrier corank at least four. This
hypothesis must be derived for each final-induction auxiliary square. -/
theorem rank_bound_of_distinct (s : SpecialData M Γ) (hne : s.F₁ ≠ s.F₂) :
    natRank M s.D + 4 ≤ natRank M M.E := by
  have hn : s.D ≠ s.F₁ := by
    intro he
    have h12 : s.F₁ ⊆ s.F₂ := he ▸ s.D_subset_second
    have hr1 : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
    have hr2 : natRank M s.F₂ + 3 = natRank M M.E := s.second_rank
    exact hne (flat_eq_of_subset_of_natRank_le s.first_indec.1 s.second_indec.1 h12 (by omega))
  have hlt := natRank_lt_of_flat_ssubset s.D_indec.1 s.first_indec.1
    (Set.ssubset_iff_subset_ne.mpr ⟨s.D_subset_first,hn⟩)
  change natRank M s.D < natRank M s.F₁ at hlt
  have hr : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
  omega

/-- The final proof may use Lower for smaller auxiliary squares or Special
at the current corank. No recursion on Special or contraction of Lower occurs. -/
theorem null_of_carrier_bound (s : SpecialData M Γ) (hM : Connected M)
    (hΓ : ModularCut M Γ) {n : ℕ} (hlower : Lower M Γ n)
    (hne : s.F₁ ≠ s.F₂) (hr : natRank M M.E - natRank M s.D ≤ n+1) :
    NullHomotopic M Γ s.path := by
  by_cases hlo : natRank M M.E - natRank M s.D ≤ n
  · apply hlower s.path
    · rfl
    · intro i; fin_cases i
      · exact s.offW
      · exact s.offX
      · exact s.offY
      · exact s.offZ
      · exact s.offW
    · simpa only [s.carrier] using hlo
  · have hrk := s.rank_bound_of_distinct hne
    have hle := natRank_mono (M := M) s.D_indec.1.subset_ground
    exact s.null_of_lower hM hΓ (by omega) hlower (by omega)
end TutteFormalization.Homotopy.SpecialData
