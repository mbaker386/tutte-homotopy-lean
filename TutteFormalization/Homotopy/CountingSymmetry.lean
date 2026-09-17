import TutteFormalization.Homotopy.CountingFrame
import TutteFormalization.Homotopy.SpecialSymmetry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
namespace SpecialData
/-- Exchange the two corank-three flats by reversing the actual square. -/
def flip (s : SpecialData M Γ) : SpecialData M Γ where
  W := s.W
  X := s.Z
  Y := s.Y
  Z := s.X
  hW := s.hW
  hX := s.hZ
  hY := s.hY
  hZ := s.hX
  hWX := s.hZW.symm
  hXY := s.hYZ.symm
  hYZ := s.hXY.symm
  hZW := s.hWX.symm
  offW := s.offW
  offX := s.offZ
  offY := s.offY
  offZ := s.offX
  first_indec := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.second_indec
  second_indec := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.first_indec
  first_rank := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.second_rank
  second_rank := by simpa only [Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using s.first_rank
  middle_corank := s.middle_corank
  middle_decomp := s.middle_decomp
@[simp] theorem flip_D (s : SpecialData M Γ) : s.flip.D = s.D := by
  simp only [D,flip,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]
@[simp] theorem flip_first (s : SpecialData M Γ) : s.flip.F₁ = s.F₂ := by
  simp only [F₁,F₂,flip,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]
@[simp] theorem flip_second (s : SpecialData M Γ) : s.flip.F₂ = s.F₁ := by
  simp only [F₁,F₂,flip,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm]
theorem flip_typeA (s : SpecialData M Γ) (A : Set α) : s.flip.TypeA A ↔ s.TypeA A := by
  simp only [TypeA,flip_D]; rfl
theorem flip_typeB (s : SpecialData M Γ) (B : Set α) : s.flip.TypeB B ↔ s.TypeB B := by
  simp only [TypeB,flip_D]; rfl
theorem flip_path (s : SpecialData M Γ) : s.flip.path = s.path.reverse := by
  apply TuttePath.ext_vertices (p := s.flip.path) (q := s.path.reverse) rfl
  intro i; fin_cases i <;> rfl
theorem flip_null_iff (s : SpecialData M Γ) :
    NullHomotopic M Γ s.flip.path ↔ NullHomotopic M Γ s.path := by
  rw [s.flip_path,null_reverse_iff]
end SpecialData
namespace CountingFrame
variable {s : SpecialData M Γ}
def swap (c : CountingFrame s) : CountingFrame s.swap where
  T := c.T
  hT := c.hT
  offT := c.offT
  DT := by simpa only [SpecialData.swap_D] using c.DT
  rankD := by simpa only [SpecialData.swap_D] using c.rankD
  corankWT := c.corankYT
  decompWT := c.decompYT
  corankYT := c.corankWT
  decompYT := c.decompWT
def flip (c : CountingFrame s) : CountingFrame s.flip where
  T := c.T
  hT := c.hT
  offT := c.offT
  DT := by simpa only [SpecialData.flip_D] using c.DT
  rankD := by simpa only [SpecialData.flip_D] using c.rankD
  corankWT := c.corankWT
  decompWT := c.decompWT
  corankYT := c.corankYT
  decompYT := c.decompYT
end CountingFrame
end TutteFormalization.Homotopy
