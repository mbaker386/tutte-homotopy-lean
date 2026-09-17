import TutteFormalization.Homotopy.ExtraPoles

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable (s : SpecialData M Γ)

/-- The triple intersection for the auxiliary special square in the extra-flat case. -/
theorem extra_middle_trace {Q H : Set α} (hQ : Indecomposable M Q)
    (hrQ : natRank M Q + 3 = natRank M M.E) (hQL : Q ⊆ s.W ∩ s.Y)
    (hH : IsHyperplane M H) (hQH : Q ⊆ H) (hWH : s.W ≠ H) (hYH : s.Y ≠ H) :
    s.Y ∩ H ∩ s.W = Q := by
  have hrL := corankTwo_natRank s.middle_corank
  have hn : ¬ s.W ∩ s.Y ⊆ H := by
    intro h
    rcases (separation_hyperplanes s.hW s.hY s.middle_decomp).2 H hH h with he | he
    · exact hWH he.symm
    · exact hYH he.symm
  have ht := (hyperplane_inter_of_cover hQ.1 s.middle_corank.1 hH hQL hQH (by omega) hn).1
  simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using ht

/-- Replace only the second special flat by a third one through an actual
off-cut hyperplane; all adjacency and triple-intersection premises are derived. -/
def withSecond {Q H : Set α} (hQ : Indecomposable M Q)
    (hrQ : natRank M Q + 3 = natRank M M.E) (hQL : Q ⊆ s.W ∩ s.Y)
    (hH : IsHyperplane M H) (hoH : H ∉ Γ) (hQH : Q ⊆ H)
    (hWH : s.W ≠ H) (hYH : s.Y ≠ H) : SpecialData M Γ where
  W := s.W
  X := s.X
  Y := s.Y
  Z := H
  hW := s.hW
  hX := s.hX
  hY := s.hY
  hZ := hH
  hWX := s.hWX
  hXY := s.hXY
  hYZ := (third_hyperplane_adjacent hQ hrQ s.middle_corank s.middle_decomp hQL
    s.hW s.hY s.W_ne_Y Set.inter_subset_left Set.inter_subset_right hH hWH hYH hQH).2.symm
  hZW := (third_hyperplane_adjacent hQ hrQ s.middle_corank s.middle_decomp hQL
    s.hW s.hY s.W_ne_Y Set.inter_subset_left Set.inter_subset_right hH hWH hYH hQH).1
  offW := s.offW
  offX := s.offX
  offY := s.offY
  offZ := hoH
  first_indec := s.first_indec
  first_rank := s.first_rank
  second_indec := (s.extra_middle_trace hQ hrQ hQL hH hQH hWH hYH).symm ▸ hQ
  second_rank := (s.extra_middle_trace hQ hrQ hQL hH hQH hWH hYH).symm ▸ hrQ
  middle_corank := s.middle_corank
  middle_decomp := s.middle_decomp

variable {Q H : Set α} (hQ : Indecomposable M Q)
  (hrQ : natRank M Q + 3 = natRank M M.E) (hQL : Q ⊆ s.W ∩ s.Y)
  (hH : IsHyperplane M H) (hoH : H ∉ Γ) (hQH : Q ⊆ H)
  (hWH : s.W ≠ H) (hYH : s.Y ≠ H)

theorem withSecond_second :
    (s.withSecond hQ hrQ hQL hH hoH hQH hWH hYH).F₂ = Q :=
  s.extra_middle_trace hQ hrQ hQL hH hQH hWH hYH

theorem withSecond_D (hrD : natRank M s.D + 4 = natRank M M.E)
    (hDQ : s.D ⊆ Q) (hne : s.F₁ ≠ Q) :
    (s.withSecond hQ hrQ hQL hH hoH hQH hWH hYH).D = s.D := by
  have hrF : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
  have hi := cover_flats_inter_eq s.D_indec.1 s.first_indec.1 hQ.1
    s.D_subset_first hDQ (by omega : natRank M s.F₁ = natRank M s.D + 1) (by omega) hne
  have ht := s.extra_middle_trace hQ hrQ hQL hH hQH hWH hYH
  change s.W ∩ s.X ∩ s.Y ∩ H = s.D
  rw [← hi,← ht]
  ext x
  constructor
  · intro hx; exact ⟨hx.1,⟨⟨hx.1.2,hx.2⟩,hx.1.1.1⟩⟩
  · intro hx; exact ⟨hx.1,hx.2.1.2⟩

/-- Same-corank auxiliary nullity uses the earlier pole obstruction, never
recursion through Special or the unfinished homotopy theorem. -/
theorem withSecond_null (hM : Connected M) (hΓ : ModularCut M Γ) (hlower : Lower M Γ 3)
    (hrD : natRank M s.D + 4 = natRank M M.E) (hDQ : s.D ⊆ Q) (hne : s.F₁ ≠ Q)
    {B : Set α} (hb : s.TypeB B) (hoFirst : M.closure (B ∪ s.F₁) ∉ Γ)
    (hoExtra : M.closure (B ∪ Q) ∉ Γ) :
    NullHomotopic M Γ (s.withSecond hQ hrQ hQL hH hoH hQH hWH hYH).path := by
  let t := s.withSecond hQ hrQ hQL hH hoH hQH hWH hYH
  have hd : t.D = s.D := s.withSecond_D hQ hrQ hQL hH hoH hQH hWH hYH hrD hDQ hne
  have htB : t.TypeB B := by
    change Indecomposable M B ∧ t.D ⊆ B ∧ natRank M B = natRank M t.D + 2 ∧ ¬ B ⊆ s.W ∧ ¬ B ⊆ s.Y
    rw [hd]
    exact hb
  have hr : natRank M t.D + (3+1) = natRank M M.E := by simpa only [hd] using hrD
  by_contra hn
  have hp := t.pole_in_cut hM hΓ (by decide : 3 ≤ 3) hlower hr hn htB
  have hsecond : t.F₂ = Q := s.withSecond_second hQ hrQ hQL hH hoH hQH hWH hYH
  rw [hsecond] at hp
  exact hp.elim hoFirst hoExtra
end TutteFormalization.Homotopy.SpecialData
