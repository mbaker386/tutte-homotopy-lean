import TutteFormalization.Homotopy.SecondIntersection
import TutteFormalization.Homotopy.TransversalJoin
import TutteFormalization.Homotopy.ThreePlaneCoverage

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The geometric three-plane configuration constructed before the counting
block. No counts, recognition, or deformation conclusions are assumed as fields. -/
structure CountingFrame (s : SpecialData M Γ) where
  T : Set α
  hT : IsHyperplane M T
  offT : T ∉ Γ
  DT : s.D ⊆ T
  rankD : natRank M s.D + 4 = natRank M M.E
  corankWT : CorankTwo M (s.W ∩ T)
  decompWT : ¬ Indecomposable M (s.W ∩ T)
  corankYT : CorankTwo M (s.Y ∩ T)
  decompYT : ¬ Indecomposable M (s.Y ∩ T)

namespace SpecialData

theorem exists_countingFrame (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hrD : natRank M s.D + 4 = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) : Nonempty (CountingFrame s) := by
  obtain ⟨A,B,C,ha,hAW,hnAY,hb,hc,hAB,hAC,hoB,hiB,hiC,hoC,hBC,hinter⟩ :=
    s.exists_opposite_poles hM hΓ (by decide : 3 ≤ 3) hlower hrD hnot
  let T := M.closure (B ∪ C)
  have hBT : B ⊆ T := M.subset_closure_of_subset' Set.subset_union_left hb.1.1.subset_ground
  have hCT : C ⊆ T := M.subset_closure_of_subset' Set.subset_union_right hc.1.1.subset_ground
  have hrA := ha.2.2.1
  have hrB := hb.2.2.1
  have hrC := hc.2.2.1
  have hrT := rank_join_of_distinct_covers hb.1.1 hc.1.1 (by omega) (by omega) hBC hinter
  have hT : IsHyperplane M T := by
    apply isHyperplane_of_natRank (M.isFlat_closure _)
    omega
  obtain ⟨I,hI,hTI,hIo⟩ := s.exists_off_above_join hΓ (by decide : 3 ≤ 3) hrD
    ha hb hc hBC hinter hoB hiC hoC
  have hoT : T ∉ Γ := fun h => hIo (hΓ.upward T I h hI.1 hTI)
  have hw := s.second_intersection_decomposable hM hΓ (by decide : 3 ≤ 3) hlower hrD hnot
    ha hb hc hAW hAB hAC hoB hoC hT hBT hCT hoT
  have hy := s.first_intersection_decomposable hM hΓ (by decide : 3 ≤ 3) hlower hrD hnot
    ha hb hc hAW hAB hAC hoB hoC hT hBT hCT hoT
  exact ⟨⟨T,hT,hoT,hb.2.1.trans hBT,hrD,hw.2,hw.1,hy.2,hy.1⟩⟩
end SpecialData
namespace CountingFrame
variable {s : SpecialData M Γ} (c : CountingFrame s)

theorem cover_below_pair {P : Set α} (hP : M.IsFlat P) (hDP : s.D ⊆ P)
    (hrP : natRank M P = natRank M s.D + 1) :
    P ⊆ s.W ∩ s.Y ∨ P ⊆ s.W ∩ c.T ∨ P ⊆ s.Y ∩ c.T :=
  cover_below_pair_plane s.D_indec.1 hP hDP hrP s.hW.1 s.hY.1 c.hT.1
    s.D_subset_W s.D_subset_Y c.DT s.W_union_Y
    (separation_hyperplanes s.hW c.hT c.decompWT).1 (separation_hyperplanes s.hY c.hT c.decompYT).1

theorem corankTwo_below {L : Set α} (hL : CorankTwo M L) (hDL : s.D ⊆ L) :
    L ⊆ s.W ∨ L ⊆ s.Y ∨ L ⊆ c.T :=
  corankTwo_below_three_planes s.D_indec.1 c.rankD hL hDL s.hW s.hY c.hT
    s.D_subset_W s.D_subset_Y c.DT s.middle_corank s.middle_decomp
    c.corankWT c.decompWT c.corankYT c.decompYT

theorem typeA_below_T {A : Set α} (ha : s.TypeA A) : A ⊆ c.T := by
  rcases c.cover_below_pair ha.1.1 ha.2.1 ha.2.2.1 with h | h | h
  · exact False.elim (ha.2.2.2 h)
  · exact h.trans Set.inter_subset_right
  · exact h.trans Set.inter_subset_right

theorem typeA_one_side {A : Set α} (ha : s.TypeA A) :
    (A ⊆ s.W ∧ ¬ A ⊆ s.Y) ∨ (A ⊆ s.Y ∧ ¬ A ⊆ s.W) := by
  have hh := flat_cover_under_one_side s.D_indec.1 ha.1.1 ha.2.1 ha.2.2.1
    s.hW.1 s.hY.1 s.D_subset_W s.D_subset_Y s.W_union_Y
  rcases hh with hw | hy
  · exact Or.inl ⟨hw,fun hy => ha.2.2.2 (Set.subset_inter hw hy)⟩
  · exact Or.inr ⟨hy,fun hw => ha.2.2.2 (Set.subset_inter hw hy)⟩

theorem typeB_below_T {B : Set α} (hb : s.TypeB B) : B ⊆ c.T := by
  have hcB : CorankTwo M B := (corankTwo_iff_natRank hb.1.1).mpr (by
    have := hb.2.2.1; have := c.rankD; omega)
  rcases c.corankTwo_below hcB hb.2.1 with h | h | h
  · exact False.elim (hb.2.2.2.1 h)
  · exact False.elim (hb.2.2.2.2 h)
  · exact h
end CountingFrame
end TutteFormalization.Homotopy
