import TutteFormalization.Homotopy.TwoLineCuts

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)
include c

/-- B.27: exactly two indecomposable corank-two flats lie between F₁ and W. -/
theorem first_two_lines_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ L K, Indecomposable M L ∧ Indecomposable M K ∧ CorankTwo M L ∧ CorankTwo M K ∧
      s.F₁ ⊆ L ∧ s.F₁ ⊆ K ∧ L ⊆ s.W ∧ K ⊆ s.W ∧ L ≠ K ∧
      ∀ J, Indecomposable M J → CorankTwo M J → s.F₁ ⊆ J → J ⊆ s.W → J = L ∨ J = K :=
  two_lines_of_pencil_count s.first_indec s.first_rank s.hW s.hY
    (fun _ h => h.1.1) Set.inter_subset_right s.middle_corank s.middle_decomp
    (fun _ hi hc hF hY => c.first_line_three_on_Y hM hΓ hlower hnot hi hc hF hY)

theorem first_two_lines_on_Y (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ L K, Indecomposable M L ∧ Indecomposable M K ∧ CorankTwo M L ∧ CorankTwo M K ∧
      s.F₁ ⊆ L ∧ s.F₁ ⊆ K ∧ L ⊆ s.Y ∧ K ⊆ s.Y ∧ L ≠ K ∧
      ∀ J, Indecomposable M J → CorankTwo M J → s.F₁ ⊆ J → J ⊆ s.Y → J = L ∨ J = K := by
  have hh := c.swap.first_two_lines_on_W hM hΓ hlower
    (fun h => hnot ((s.swap_null_iff hΓ).mp h))
  rw [s.swap_first] at hh
  exact hh

theorem first_two_cut_hyperplanes (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ s.F₁ ⊆ U ∧ s.F₁ ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → s.F₁ ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  obtain ⟨L,K,hL,hK,hcL,hcK,hFL,hFK,hLW,hKW,hLK,all⟩ := c.first_two_lines_on_W hM hΓ hlower hnot
  exact two_cut_of_two_lines hΓ s.first_indec s.first_rank s.hW s.hY s.W_ne_Y s.offW s.offY
    (fun _ h => h.1.1) Set.inter_subset_right s.middle_corank s.middle_decomp
    hcL hcK hFL hFK hLW hKW hLK all
    (c.first_line_three_on_W hM hΓ hlower hnot hL hcL hFL hLW)
    (c.first_line_three_on_W hM hΓ hlower hnot hK hcK hFK hKW)

theorem second_two_lines_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ L K, Indecomposable M L ∧ Indecomposable M K ∧ CorankTwo M L ∧ CorankTwo M K ∧
      s.F₂ ⊆ L ∧ s.F₂ ⊆ K ∧ L ⊆ s.W ∧ K ⊆ s.W ∧ L ≠ K ∧
      ∀ J, Indecomposable M J → CorankTwo M J → s.F₂ ⊆ J → J ⊆ s.W → J = L ∨ J = K := by
  have hh := c.flip.first_two_lines_on_W hM hΓ hlower (fun h => hnot (s.flip_null_iff.mp h))
  rw [s.flip_first] at hh
  exact hh

theorem second_two_lines_on_Y (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ L K, Indecomposable M L ∧ Indecomposable M K ∧ CorankTwo M L ∧ CorankTwo M K ∧
      s.F₂ ⊆ L ∧ s.F₂ ⊆ K ∧ L ⊆ s.Y ∧ K ⊆ s.Y ∧ L ≠ K ∧
      ∀ J, Indecomposable M J → CorankTwo M J → s.F₂ ⊆ J → J ⊆ s.Y → J = L ∨ J = K := by
  have hh := c.flip.first_two_lines_on_Y hM hΓ hlower (fun h => hnot (s.flip_null_iff.mp h))
  rw [s.flip_first] at hh
  exact hh

theorem second_two_cut_hyperplanes (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ s.F₂ ⊆ U ∧ s.F₂ ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → s.F₂ ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  have hh := c.flip.first_two_cut_hyperplanes hM hΓ hlower (fun h => hnot (s.flip_null_iff.mp h))
  rw [s.flip_first] at hh
  exact hh
end TutteFormalization.Homotopy.CountingFrame
