import TutteFormalization.Homotopy.SpecialData
import TutteFormalization.Homotopy.SquareSymmetry

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.21's specified exchange of W and Y, with the corresponding reversed
half-rotation of the square. -/
def swap (s : SpecialData M Γ) : SpecialData M Γ where
  W := s.Y
  X := s.X
  Y := s.W
  Z := s.Z
  hW := s.hY
  hX := s.hX
  hY := s.hW
  hZ := s.hZ
  hWX := s.hXY.symm
  hXY := s.hWX.symm
  hYZ := s.hZW.symm
  hZW := s.hYZ.symm
  offW := s.offY
  offX := s.offX
  offY := s.offW
  offZ := s.offZ
  first_indec := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.first_indec
  second_indec := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.second_indec
  first_rank := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.first_rank
  second_rank := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.second_rank
  middle_corank := by simpa only [Set.inter_comm] using s.middle_corank
  middle_decomp := by simpa only [Set.inter_comm] using s.middle_decomp

@[simp] theorem swap_D (s : SpecialData M Γ) : s.swap.D = s.D := by
  simp only [D,swap,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]
@[simp] theorem swap_first (s : SpecialData M Γ) : s.swap.F₁ = s.F₁ := by
  simp only [F₁,swap,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]
@[simp] theorem swap_second (s : SpecialData M Γ) : s.swap.F₂ = s.F₂ := by
  simp only [F₂,swap,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]

theorem swap_typeA (s : SpecialData M Γ) (A : Set α) : s.swap.TypeA A ↔ s.TypeA A := by
  simp only [TypeA,swap_D]
  change (_ ∧ _ ∧ _ ∧ ¬ A ⊆ s.Y ∩ s.W) ↔ _
  rw [Set.inter_comm s.Y s.W]

theorem swap_typeB (s : SpecialData M Γ) (B : Set α) : s.swap.TypeB B ↔ s.TypeB B := by
  simp only [TypeB,swap_D]
  change (_ ∧ _ ∧ _ ∧ ¬ B ⊆ s.Y ∧ ¬ B ⊆ s.W) ↔ _
  tauto

theorem swap_null_iff (s : SpecialData M Γ) (hΓ : ModularCut M Γ) :
    NullHomotopic M Γ s.swap.path ↔ NullHomotopic M Γ s.path :=
  square_swap_null_iff hΓ s.hW s.hX s.hY s.hZ s.hWX s.hXY s.hYZ s.hZW
end TutteFormalization.Homotopy.SpecialData
