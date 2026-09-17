import TutteFormalization.Homotopy.SpecialEdges
import TutteFormalization.Homotopy.SquareBridge

namespace TutteFormalization.Homotopy
variable {α : Type*} (M : Matroid α) [M.Finite] (Γ : Set (Set α))

/-- Internal data for the manuscript's special path, with every geometric and
path-validity condition explicit. No deformation or structural conclusion is a field. -/
structure SpecialData where
  W : Set α
  X : Set α
  Y : Set α
  Z : Set α
  hW : IsHyperplane M W
  hX : IsHyperplane M X
  hY : IsHyperplane M Y
  hZ : IsHyperplane M Z
  hWX : TutteAdjacent M W X
  hXY : TutteAdjacent M X Y
  hYZ : TutteAdjacent M Y Z
  hZW : TutteAdjacent M Z W
  offW : W ∉ Γ
  offX : X ∉ Γ
  offY : Y ∉ Γ
  offZ : Z ∉ Γ
  first_indec : Indecomposable M (W ∩ X ∩ Y)
  second_indec : Indecomposable M (Y ∩ Z ∩ W)
  first_rank : natRank M (W ∩ X ∩ Y) + 3 = natRank M M.E
  second_rank : natRank M (Y ∩ Z ∩ W) + 3 = natRank M M.E
  middle_corank : CorankTwo M (W ∩ Y)
  middle_decomp : ¬ Indecomposable M (W ∩ Y)

namespace SpecialData
variable {M Γ} (s : SpecialData M Γ)
def path : TuttePath M := TuttePath.square s.hW s.hX s.hY s.hZ s.hWX s.hXY s.hYZ s.hZW
def D : Set α := s.W ∩ s.X ∩ s.Y ∩ s.Z
def F₁ : Set α := s.W ∩ s.X ∩ s.Y
def F₂ : Set α := s.Y ∩ s.Z ∩ s.W

theorem carrier : s.path.carrier = s.D := TuttePath.square_carrier _ _ _ _ _ _ _ _
theorem D_indec : Indecomposable M s.D := s.carrier ▸ s.path.carrier_indecomposable

theorem D_subset_first : s.D ⊆ s.F₁ := Set.inter_subset_left

theorem D_subset_second : s.D ⊆ s.F₂ := by
  intro a ha
  exact ⟨⟨ha.1.2,ha.2⟩,ha.1.1.1⟩

theorem D_subset_W : s.D ⊆ s.W := fun _ ha => ha.1.1.1
theorem D_subset_Y : s.D ⊆ s.Y := fun _ ha => ha.1.2

theorem W_ne_Y : s.W ≠ s.Y := by
  intro heq
  have hc := corankTwo_natRank s.middle_corank
  have hh := hyperplane_natRank s.hY
  rw [heq,Set.inter_self] at hc
  omega

theorem W_union_Y : s.W ∪ s.Y = M.E :=
  (separation_hyperplanes s.hW s.hY s.middle_decomp).1

/-- B.11/12: corank is expressed by the equivalent rank increment above D. -/
def TypeA (A : Set α) : Prop := Indecomposable M A ∧ s.D ⊆ A ∧
  natRank M A = natRank M s.D + 1 ∧ ¬ A ⊆ s.W ∩ s.Y

def TypeB (B : Set α) : Prop := Indecomposable M B ∧ s.D ⊆ B ∧
  natRank M B = natRank M s.D + 2 ∧ ¬ B ⊆ s.W ∧ ¬ B ⊆ s.Y

theorem typeA_first_join {A : Set α} (ha : s.TypeA A) :
    Indecomposable M (M.closure (A ∪ s.F₁)) ∧ CorankTwo M (M.closure (A ∪ s.F₁)) :=
  transversal_cover_join s.first_indec s.first_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.1.1,ha.2⟩) ha.1.1 ha.2.1 s.D_subset_first ha.2.2.1 ha.2.2.2

theorem typeA_second_join {A : Set α} (ha : s.TypeA A) :
    Indecomposable M (M.closure (A ∪ s.F₂)) ∧ CorankTwo M (M.closure (A ∪ s.F₂)) :=
  transversal_cover_join s.second_indec s.second_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.2,ha.1.1⟩) ha.1.1 ha.2.1 s.D_subset_second ha.2.2.1 ha.2.2.2

theorem typeB_first_pole {B : Set α} (hb : s.TypeB B) :
    IsHyperplane M (M.closure (B ∪ s.F₁)) :=
  transversal_two_join_hyperplane s.first_indec s.first_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.1.1,ha.2⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right hb.1.1 hb.2.1 s.D_subset_first
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2

theorem typeB_second_pole {B : Set α} (hb : s.TypeB B) :
    IsHyperplane M (M.closure (B ∪ s.F₂)) :=
  transversal_two_join_hyperplane s.second_indec s.second_rank s.middle_corank s.middle_decomp
    (by intro a ha; exact ⟨ha.2,ha.1.1⟩) s.hW s.hY s.W_ne_Y
    Set.inter_subset_left Set.inter_subset_right hb.1.1 hb.2.1 s.D_subset_second
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2

theorem typeB_intersections {B : Set α} (hb : s.TypeB B) :
    Indecomposable M (B ∩ s.W) ∧ Indecomposable M (B ∩ s.Y) ∧
      natRank M (B ∩ s.W) = natRank M s.D + 1 ∧
      natRank M (B ∩ s.Y) = natRank M s.D + 1 ∧
      (B ∩ s.W) ∩ (B ∩ s.Y) = s.D ∧ M.closure ((B ∩ s.W) ∪ (B ∩ s.Y)) = B :=
  transversal_intersections s.D_indec hb.1 hb.2.1 hb.2.2.1 s.hW s.hY
    s.D_subset_W s.D_subset_Y s.W_union_Y hb.2.2.2.1 hb.2.2.2.2
end SpecialData
end TutteFormalization.Homotopy
