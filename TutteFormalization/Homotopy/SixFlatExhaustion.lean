import TutteFormalization.Homotopy.ExtraFlat

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)

include c in
theorem first_ne_second : s.F₁ ≠ s.F₂ := by
  intro he
  have hsub : s.F₁ ⊆ s.D := by
    intro x hx
    have hx₂ : x ∈ s.F₂ := he ▸ hx
    exact ⟨hx,hx₂.1.2⟩
  have heD := Set.Subset.antisymm hsub s.D_subset_first
  have hrF : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
  have hrD := c.rankD
  rw [heD] at hrF
  omega

include c in
/-- Under non-nullness, the extra-flat branch excludes every other flat on
W∩Y. This is the manuscript's final dichotomy, not a recognition assumption. -/
theorem corankThree_classification (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {P : Set α} (hP : Indecomposable M P) (hDP : s.D ⊆ P)
    (hrP : natRank M P + 3 = natRank M M.E) : P = s.F₁ ∨ P = s.F₂ ∨ s.TypeA P := by
  by_cases h₁ : P = s.F₁
  · exact Or.inl h₁
  by_cases h₂ : P = s.F₂
  · exact Or.inr (Or.inl h₂)
  right; right
  refine ⟨hP,hDP,?_,?_⟩
  · have := c.rankD; omega
  · intro hPL
    exact hnot (c.null_of_extra_flat hM hΓ hlower hP hrP hDP hPL (Ne.symm h₁) (Ne.symm h₂))

include c in
/-- Exactly the six corank-three indecomposable flats required at B.28:
the four displayed type-(a) witnesses and the two special flats exhaust them. -/
theorem six_flat_exhaustion (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ A B C D, s.TypeA A ∧ s.TypeA B ∧ s.TypeA C ∧ s.TypeA D ∧
      A ⊆ s.W ∧ B ⊆ s.W ∧ C ⊆ s.Y ∧ D ⊆ s.Y ∧ A ≠ B ∧ C ≠ D ∧
      A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧
      ∀ P, Indecomposable M P → s.D ⊆ P → natRank M P + 3 = natRank M M.E →
        P = s.F₁ ∨ P = s.F₂ ∨ P = A ∨ P = B ∨ P = C ∨ P = D := by
  obtain ⟨A,B,C,D,ha,hb,hc,hd,hAW,hBW,hCY,hDY,hAB,hCD,hAC,hAD,hBC,hBD,all⟩ :=
    c.four_typeA hM hΓ hlower hnot
  refine ⟨A,B,C,D,ha,hb,hc,hd,hAW,hBW,hCY,hDY,hAB,hCD,hAC,hAD,hBC,hBD,?_⟩
  intro P hP hDP hrP
  rcases c.corankThree_classification hM hΓ hlower hnot hP hDP hrP with he | he | haP
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (all P haP))
end TutteFormalization.Homotopy.CountingFrame
