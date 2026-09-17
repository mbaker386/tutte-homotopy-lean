import TutteFormalization.Homotopy.SpecialCounts

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)

/-- The trace identity used after B.27 and in the extra-flat branch. -/
theorem typeA_first_trace {A : Set α} (ha : s.TypeA A) :
    M.closure (A ∪ s.F₁) ∩ c.T = A := by
  have hj := s.typeA_first_join ha
  have hrj := corankTwo_natRank hj.2
  have hra := ha.2.2.1
  have hrd := c.rankD
  exact (hyperplane_inter_of_cover ha.1.1 hj.1.1 c.hT
    (M.subset_closure_of_subset' Set.subset_union_left ha.1.1.subset_ground)
    (c.typeA_below_T ha) (by omega)
    (fun h => c.first_not_below_T
      ((M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground).trans h))).1

include c in
theorem typeA_first_injective {A B : Set α} (ha : s.TypeA A) (hb : s.TypeA B)
    (he : M.closure (A ∪ s.F₁) = M.closure (B ∪ s.F₁)) : A = B :=
  (c.typeA_first_trace ha).symm.trans ((congrArg (fun Z => Z ∩ c.T) he).trans (c.typeA_first_trace hb))

include c in
/-- B.27 and its following paragraph, with the exhaustion used in the
extra-flat branch: precisely four type-(a) transversals, two on each side. -/
theorem four_typeA (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) :
    ∃ A B C D, s.TypeA A ∧ s.TypeA B ∧ s.TypeA C ∧ s.TypeA D ∧
      A ⊆ s.W ∧ B ⊆ s.W ∧ C ⊆ s.Y ∧ D ⊆ s.Y ∧ A ≠ B ∧ C ≠ D ∧
      A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧
      ∀ P, s.TypeA P → P = A ∨ P = B ∨ P = C ∨ P = D := by
  obtain ⟨L,K,hL,hK,hcL,hcK,hFL,hFK,hLW,hKW,hLK,allW⟩ := c.first_two_lines_on_W hM hΓ hlower hnot
  obtain ⟨U,V,hU,hV,hcU,hcV,hFU,hFV,hUY,hVY,hUV,allY⟩ := c.first_two_lines_on_Y hM hΓ hlower hnot
  obtain ⟨A,ha,hAL⟩ := c.exists_typeA_below hL hcL (s.D_subset_first.trans hFL)
  obtain ⟨B,hb,hBK⟩ := c.exists_typeA_below hK hcK (s.D_subset_first.trans hFK)
  obtain ⟨C,hc,hCU⟩ := c.exists_typeA_below hU hcU (s.D_subset_first.trans hFU)
  obtain ⟨D,hd,hDV⟩ := c.exists_typeA_below hV hcV (s.D_subset_first.trans hFV)
  have haeq := c.first_join_eq ha hcL hAL hFL
  have hbeq := c.first_join_eq hb hcK hBK hFK
  have hceq := c.first_join_eq hc hcU hCU hFU
  have hdeq := c.first_join_eq hd hcV hDV hFV
  have hAW := hAL.trans hLW
  have hBW := hBK.trans hKW
  have hCY := hCU.trans hUY
  have hDY := hDV.trans hVY
  have cross {R S : Set α} (hr : s.TypeA R) (hrW : R ⊆ s.W) (hsY : S ⊆ s.Y) : R ≠ S :=
    fun he => hr.2.2.2 (Set.subset_inter hrW (he ▸ hsY))
  refine ⟨A,B,C,D,ha,hb,hc,hd,hAW,hBW,hCY,hDY,?_,?_,
    cross ha hAW hCY,cross ha hAW hDY,cross hb hBW hCY,cross hb hBW hDY,?_⟩
  · intro he
    exact hLK (haeq.symm.trans ((congrArg (fun Z => M.closure (Z ∪ s.F₁)) he).trans hbeq))
  · intro he
    exact hUV (hceq.symm.trans ((congrArg (fun Z => M.closure (Z ∪ s.F₁)) he).trans hdeq))
  · intro P hp
    have hj := s.typeA_first_join hp
    have hFj : s.F₁ ⊆ M.closure (P ∪ s.F₁) :=
      M.subset_closure_of_subset' Set.subset_union_right s.first_indec.1.subset_ground
    rcases typeA_one_side hp with ⟨hw,_⟩ | ⟨hy,_⟩
    · have hjW : M.closure (P ∪ s.F₁) ⊆ s.W :=
        (M.closure_mono (Set.union_subset hw (fun _ h => h.1.1))).trans_eq s.hW.1.closure
      rcases allW _ hj.1 hj.2 hFj hjW with he | he
      · exact Or.inl (c.typeA_first_injective hp ha (he.trans haeq.symm))
      · exact Or.inr (Or.inl (c.typeA_first_injective hp hb (he.trans hbeq.symm)))
    · have hjY : M.closure (P ∪ s.F₁) ⊆ s.Y :=
        (M.closure_mono (Set.union_subset hy Set.inter_subset_right)).trans_eq s.hY.1.closure
      rcases allY _ hj.1 hj.2 hFj hjY with he | he
      · exact Or.inr (Or.inr (Or.inl (c.typeA_first_injective hp hc (he.trans hceq.symm))))
      · exact Or.inr (Or.inr (Or.inr (c.typeA_first_injective hp hd (he.trans hdeq.symm))))
end TutteFormalization.Homotopy.CountingFrame
