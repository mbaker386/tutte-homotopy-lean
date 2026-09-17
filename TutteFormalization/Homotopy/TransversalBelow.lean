import TutteFormalization.Homotopy.PencilCounts

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)
include c

/-- B.27's Diamond argument: each indecomposable corank-two flat above D
contains a type-(a) transversal. -/
theorem exists_typeA_below {L : Set α} (hL : Indecomposable M L)
    (hcL : CorankTwo M L) (hDL : s.D ⊆ L) :
    ∃ A, s.TypeA A ∧ A ⊆ L := by
  have hrL := corankTwo_natRank hcL
  have hrD := c.rankD
  obtain ⟨A,B,hA,hB,hDA,hDB,hAL,hBL,hAB,hrA,hrB⟩ :=
    exists_indecomposable_diamond hL s.D_indec hDL (by omega)
  have hj := cover_flats_join_eq hL.1 hA.1 hB.1 hAL hBL hrA hrB (by omega) hAB
  have hnL : ¬ L ⊆ s.W ∩ s.Y := by
    intro h
    have hr := corankTwo_natRank s.middle_corank
    have he := flat_eq_of_subset_of_natRank_le hL.1 s.middle_corank.1 h (by omega)
    exact s.middle_decomp (he ▸ hL)
  by_cases hnA : A ⊆ s.W ∩ s.Y
  · have hnB : ¬ B ⊆ s.W ∩ s.Y := by
      intro h
      exact hnL (hj ▸ (M.closure_mono (Set.union_subset hnA h)).trans_eq s.middle_corank.1.closure)
    exact ⟨B,⟨hB,hDB,by omega,hnB⟩,hBL⟩
  · exact ⟨A,⟨hA,hDA,by omega,hnA⟩,hAL⟩

theorem first_join_eq {A L : Set α} (ha : s.TypeA A)
    (hcL : CorankTwo M L) (hAL : A ⊆ L) (hFL : s.F₁ ⊆ L) :
    M.closure (A ∪ s.F₁) = L := by
  have hj := s.typeA_first_join ha
  have hrJ := corankTwo_natRank hj.2
  have hrL := corankTwo_natRank hcL
  exact flat_eq_of_subset_of_natRank_le hj.1.1 hcL.1
    ((M.closure_mono (Set.union_subset hAL hFL)).trans_eq hcL.1.closure) (by omega)

/-- B.27's application of the actual B.26 count to every line above F₁ on W. -/
theorem first_line_three_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {L : Set α} (hL : Indecomposable M L) (hcL : CorankTwo M L)
    (hFL : s.F₁ ⊆ L) (hLW : L ⊆ s.W) : ThreePencil M Γ L s.W := by
  obtain ⟨A,ha,hAL⟩ := c.exists_typeA_below hL hcL (s.D_subset_first.trans hFL)
  have hcount := c.first_three_on_W hM hΓ hlower hnot ha (hAL.trans hLW)
  rwa [c.first_join_eq ha hcL hAL hFL] at hcount

theorem first_line_three_on_Y (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {L : Set α} (hL : Indecomposable M L) (hcL : CorankTwo M L)
    (hFL : s.F₁ ⊆ L) (hLY : L ⊆ s.Y) : ThreePencil M Γ L s.Y := by
  obtain ⟨A,ha,hAL⟩ := c.exists_typeA_below hL hcL (s.D_subset_first.trans hFL)
  have hcount := c.first_three_on_Y hM hΓ hlower hnot ha (hAL.trans hLY)
  rwa [c.first_join_eq ha hcL hAL hFL] at hcount
end TutteFormalization.Homotopy.CountingFrame
