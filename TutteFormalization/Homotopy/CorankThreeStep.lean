import TutteFormalization.Homotopy.FourTriangleReduction
import TutteFormalization.Homotopy.ThirdJoinRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} (M : Matroid α) [M.Finite] (Γ : Set (Set α)) (D G : Set α)

/-- Proof-only local data for Case 2.2, also used for its residual replacement
configurations. The fields describe actual flats, edges and containment;
there are no homotopy or recognition conclusions among the fields. -/
structure CorankThreeStep where
  H : Set α
  K : Set α
  J : Set α
  hH : IsHyperplane M H
  hK : IsHyperplane M K
  hJ : IsHyperplane M J
  hHK : TutteAdjacent M H K
  hKJ : TutteAdjacent M K J
  offH : H ∉ Γ
  offK : K ∉ Γ
  offJ : J ∉ Γ
  onH : D ⊆ H
  onK : D ⊆ K
  onJ : D ⊆ J
  goodH : G ⊆ H
  badK : ¬ G ⊆ K
  triple_rank : natRank M (H ∩ K ∩ J) + 3 = natRank M M.E

namespace CorankThreeStep
variable {M Γ D G} (s : CorankThreeStep M Γ D G)
def path : TuttePath M := (TuttePath.edge s.hH s.hK s.hHK).concat (TuttePath.edge s.hK s.hJ s.hKJ) rfl
def F : Set α := s.H ∩ s.K ∩ s.J
def L : Set α := M.closure (G ∪ s.F)
def Z : Set α := M.closure (s.L ∪ (s.K ∩ s.J))

theorem carrier : s.path.carrier = s.F := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨Set.mem_iInter.mp hx 0,Set.mem_iInter.mp hx 1⟩,Set.mem_iInter.mp hx 2⟩
  · rintro ⟨⟨hH,hK⟩,hJ⟩
    apply Set.mem_iInter.mpr
    intro i; fin_cases i <;> assumption

theorem F_indec : Indecomposable M s.F := s.carrier ▸ s.path.carrier_indecomposable

theorem D_subset_F : D ⊆ s.F := fun _ hx => ⟨⟨s.onH hx,s.onK hx⟩,s.onJ hx⟩

theorem F_subset_L : s.F ⊆ s.L := M.subset_closure_of_subset' Set.subset_union_right s.F_indec.1.subset_ground

theorem G_subset_L (hG : M.IsFlat G) : G ⊆ s.L := M.subset_closure_of_subset' Set.subset_union_left hG.subset_ground

theorem L_properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) :
    CorankTwo M s.L ∧ s.L ⊆ s.H ∧ s.L ∉ Γ :=
  corankThree_first_join hΓ hD hG.1 s.F_indec.1 hDG s.D_subset_F hrG s.triple_rank
    s.hH s.goodH (fun _ hx => hx.1.1) (fun _ hx => hx.1.2) s.badK s.offH

theorem Z_properties (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) :
    IsHyperplane M s.Z ∧ s.H ≠ s.Z ∧ s.K ≠ s.Z ∧ s.H ∩ s.Z = s.L ∧
      s.K ∩ s.Z = s.K ∩ s.J ∧ s.H ∩ s.K ∩ s.Z = s.F ∧
      (s.Z = s.J ∨ TutteAdjacent M s.Z s.J) := by
  have hL := s.L_properties hΓ hD hG hDG hrG
  exact next_join_geometry s.hH s.hK s.hJ s.hKJ rfl s.triple_rank hL.1
    s.F_subset_L hL.2.1 (s.G_subset_L hG.1) s.badK

/-- The local reduction predicate records only a real generated homotopy,
On D, and a strict occurrence decrease. It is a proposition, not an axiom. -/
def Reduced : Prop := ∃ q : TuttePath M, Homotopic M Γ s.path q ∧ q.On D ∧ outsideCount q G < outsideCount s.path G

theorem reduced_of_Z_off (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ}
    (hlower : Lower M Γ n) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hrD : natRank M M.E - natRank M D ≤ n+1) (hoZ : s.Z ∉ Γ) : s.Reduced :=
  off_join_shortcut hM hΓ hlower s.hH s.hK s.hJ s.hHK s.hKJ s.F_indec rfl s.triple_rank
    hD hG hDG s.D_subset_F hrG s.goodH s.badK hrD s.offH s.offK s.offJ hoZ

theorem reduced_of_cover_below {P : Set α} (hΓ : ModularCut M Γ)
    (hP : Indecomposable M P) (hcP : CorankTwo M P) (hPH : P ⊆ s.H) (hPJ : P ⊆ s.J) : s.Reduced :=
  corankThree_triangle_shortcut_decreases hΓ s.hH s.hK s.hJ s.hHK s.hKJ s.triple_rank
    hP hcP hPH hPJ s.offH s.offK s.offJ s.onH s.onJ s.badK
end CorankThreeStep
end TutteFormalization.Homotopy
