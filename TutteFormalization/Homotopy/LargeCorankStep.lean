import TutteFormalization.Homotopy.LargeJoinGeometry
import TutteFormalization.Homotopy.InsertionDescent

namespace TutteFormalization.Homotopy
variable {α : Type*} (M : Matroid α) [M.Finite] (Γ : Set (Set α)) (D G : Set α)

/-- Geometric input at the first offender in Case 2.3. -/
structure LargeCorankStep where
  H : Set α
  B : Set α
  J : Set α
  hH : IsHyperplane M H
  hB : IsHyperplane M B
  hJ : IsHyperplane M J
  hHB : TutteAdjacent M H B
  hBJ : TutteAdjacent M B J
  offH : H ∉ Γ
  offB : B ∉ Γ
  offJ : J ∉ Γ
  onH : D ⊆ H
  onB : D ⊆ B
  onJ : D ⊆ J
  goodH : G ⊆ H
  badB : ¬ G ⊆ B
  triple_rank : natRank M (H ∩ B ∩ J) + 4 ≤ natRank M M.E

namespace LargeCorankStep
variable {M Γ D G} (s : LargeCorankStep M Γ D G)
def path : TuttePath M := (TuttePath.edge s.hH s.hB s.hHB).concat (TuttePath.edge s.hB s.hJ s.hBJ) rfl
def F : Set α := s.H ∩ s.B ∩ s.J

theorem carrier : s.path.carrier = s.F := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨Set.mem_iInter.mp hx 0,Set.mem_iInter.mp hx 1⟩,Set.mem_iInter.mp hx 2⟩
  · rintro ⟨⟨hH,hB⟩,hJ⟩
    apply Set.mem_iInter.mpr
    intro i; fin_cases i <;> assumption

theorem F_indec : Indecomposable M s.F := s.carrier ▸ s.path.carrier_indecomposable

theorem D_subset_F : D ⊆ s.F := fun _ hx => ⟨⟨s.onH hx,s.onB hx⟩,s.onJ hx⟩
end LargeCorankStep

/-- The proved geometric output of Chain and Complement in Case 2.3.
No homotopy conclusion is assumed among these data. -/
structure LargeBridge {D G : Set α} (s : LargeCorankStep M Γ D G) where
  K : Set α
  P : Set α
  T : Set α
  hK : Indecomposable M K
  rankK : natRank M K + 3 = natRank M M.E
  belowK : K ⊆ s.H ∩ s.B
  hP : Indecomposable M P
  aboveP : s.F ⊂ P
  belowP : P ⊆ s.B ∩ s.J
  rankP : natRank M P = natRank M s.F + 1
  hT : IsHyperplane M T
  offT : T ∉ Γ
  goodT : G ⊆ T
  PT : P ⊆ T
  hHT : TutteAdjacent M s.H T
  neB : T ≠ s.B
  corankTB : CorankTwo M (T ∩ s.B)
  triple : s.H ∩ s.B ∩ T = K

namespace LargeCorankStep
variable {M Γ D G} (s : LargeCorankStep M Γ D G)

theorem exists_bridge (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) : Nonempty (LargeBridge M Γ s) := by
  obtain ⟨K,hK,hFK,hKA,hrK⟩ := exists_corankThree_between s.F_indec s.hHB.2.1 s.hHB.2.2
    Set.inter_subset_left s.triple_rank
  let L := M.closure (G ∪ K)
  obtain ⟨hcL,hLH,_⟩ := corankThree_first_join hΓ hD hG.1 hK.1 hDG (s.D_subset_F.trans hFK.1)
    hrG hrK s.hH s.goodH (hKA.1.trans Set.inter_subset_left) (hKA.1.trans Set.inter_subset_right) s.badB s.offH
  have hGL : G ⊆ L := M.subset_closure_of_subset' Set.subset_union_left hG.1.subset_ground
  have hKL : K ⊆ L := M.subset_closure_of_subset' Set.subset_union_right hK.1.subset_ground
  obtain ⟨T,hT,hLT,hTH,hpreferred⟩ := exists_preferred_hyperplane hΓ hcL s.hH hLH s.offH
  have hj := large_complement_join s.hB hT s.hBJ.2.2 hK.1 rfl hFK hKA.1 (hKL.trans hLT) (hGL.trans hLT) s.badB
  have hFQ : s.F ⊆ s.B ∩ s.J := fun _ hx => ⟨hx.1.2,hx.2⟩
  obtain ⟨P,hP,hFP,hPQ,hPT,hrP⟩ := exists_large_complement s.F_indec s.hBJ.2.1 hT hFQ (hFK.1.trans (hKL.trans hLT)) hj
  obtain ⟨hT',hneH,hneT,hneB,hoT',hiL,hcR,hRT',hRB,htriple,hmeet⟩ := large_join_geometry
    s.F_indec.1 hK.1 hrK hFK.1 hKA.1 hKL hcL hLH hGL s.badB hP.1 hFP hPQ hrP rfl
    s.hH s.hB hT hLT hTH hPT hpreferred
  have hLT' : L ⊆ M.closure (L ∪ P) := M.subset_closure_of_subset' Set.subset_union_left hcL.1.subset_ground
  have hPT' : P ⊆ M.closure (L ∪ P) := M.subset_closure_of_subset' Set.subset_union_right hP.1.subset_ground
  exact ⟨⟨K,P,M.closure (L ∪ P),hK,hrK,hKA.1,hP,hFP,hPQ,hrP,hT',hoT',hGL.trans hLT',hPT',
    tutteAdjacent_of_corankTwo hiL hcL s.hH hT' hneH.symm hLH hLT',hneB,hmeet.symm ▸ hcR,htriple⟩⟩
end LargeCorankStep
end TutteFormalization.Homotopy
