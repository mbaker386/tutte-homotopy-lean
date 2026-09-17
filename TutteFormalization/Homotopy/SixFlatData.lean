import TutteFormalization.Homotopy.SixFlatExhaustion

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

def CountingFrame.planes {s : SpecialData M Γ} (c : CountingFrame s) : Fin 3 → Set α :=
  ![c.T,s.Y,s.W]

/-- Derived labelled geometry for B.28. The entries are actual ambient flats;
there is no field assuming an embedding, elementary path, or null-homotopy. -/
structure SixFlatData {s : SpecialData M Γ} (c : CountingFrame s) where
  point : Fin 6 → Set α
  indec : ∀ i, Indecomposable M (point i)
  above : ∀ i, s.D ⊆ point i
  rank : ∀ i, natRank M (point i) = natRank M s.D + 1
  injective : Function.Injective point
  first : point 0 = s.F₁
  second : point 3 = s.F₂
  incidence : ∀ i j, point i ⊆ c.planes j ↔ i.val % 3 ≠ j.val
  complete : ∀ P, Indecomposable M P → s.D ⊆ P →
    natRank M P + 3 = natRank M M.E → ∃ i, point i = P

namespace CountingFrame
variable {s : SpecialData M Γ} (c : CountingFrame s)

theorem exists_sixFlatData (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) : Nonempty (SixFlatData c) := by
  obtain ⟨A,B,C,D,ha,hb,hc,hd,hAW,hBW,hCY,hDY,hAB,hCD,hAC,hAD,hBC,hBD,all⟩ :=
    c.six_flat_exhaustion hM hΓ hlower hnot
  let P : Fin 6 → Set α := ![s.F₁,A,C,s.F₂,B,D]
  have classified (i : Fin 6) : P i = s.F₁ ∨ P i = s.F₂ ∨ s.TypeA (P i) := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inr hd)
  have hF₁W : s.F₁ ⊆ s.W := fun _ h => h.1.1
  have hF₁Y : s.F₁ ⊆ s.Y := Set.inter_subset_right
  have hF₂W : s.F₂ ⊆ s.W := Set.inter_subset_right
  have hF₂Y : s.F₂ ⊆ s.Y := fun _ h => h.1.1
  have hnAY : ¬ A ⊆ s.Y := fun h => ha.2.2.2 (Set.subset_inter hAW h)
  have hnBY : ¬ B ⊆ s.Y := fun h => hb.2.2.2 (Set.subset_inter hBW h)
  have hnCW : ¬ C ⊆ s.W := fun h => hc.2.2.2 (Set.subset_inter h hCY)
  have hnDW : ¬ D ⊆ s.W := fun h => hd.2.2.2 (Set.subset_inter h hDY)
  have hAT := c.typeA_below_T ha
  have hBT := c.typeA_below_T hb
  have hCT := c.typeA_below_T hc
  have hDT := c.typeA_below_T hd
  have hnF₁T := c.first_not_below_T
  have hnF₂T := c.second_not_below_T
  have incidence : ∀ i j, P i ⊆ c.planes j ↔ i.val % 3 ≠ j.val := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [P,planes] <;> assumption
  have hFF := c.first_ne_second
  have notFirst {R : Set α} (hr : s.TypeA R) : R ≠ s.F₁ :=
    fun he => hr.2.2.2 (he ▸ Set.subset_inter hF₁W hF₁Y)
  have notSecond {R : Set α} (hr : s.TypeA R) : R ≠ s.F₂ :=
    fun he => hr.2.2.2 (he ▸ Set.subset_inter hF₂W hF₂Y)
  have hi : Function.Injective P := by
    intro i j he
    fin_cases i <;> fin_cases j <;> dsimp [P] at he
    all_goals first
      | rfl
      | exact False.elim (hFF he)
      | exact False.elim (hFF he.symm)
      | exact False.elim (notFirst ha he)
      | exact False.elim (notFirst ha he.symm)
      | exact False.elim (notFirst hb he)
      | exact False.elim (notFirst hb he.symm)
      | exact False.elim (notFirst hc he)
      | exact False.elim (notFirst hc he.symm)
      | exact False.elim (notFirst hd he)
      | exact False.elim (notFirst hd he.symm)
      | exact False.elim (notSecond ha he)
      | exact False.elim (notSecond ha he.symm)
      | exact False.elim (notSecond hb he)
      | exact False.elim (notSecond hb he.symm)
      | exact False.elim (notSecond hc he)
      | exact False.elim (notSecond hc he.symm)
      | exact False.elim (notSecond hd he)
      | exact False.elim (notSecond hd he.symm)
      | exact False.elim (hAB he)
      | exact False.elim (hAB he.symm)
      | exact False.elim (hCD he)
      | exact False.elim (hCD he.symm)
      | exact False.elim (hAC he)
      | exact False.elim (hAC he.symm)
      | exact False.elim (hAD he)
      | exact False.elim (hAD he.symm)
      | exact False.elim (hBC he)
      | exact False.elim (hBC he.symm)
      | exact False.elim (hBD he)
      | exact False.elim (hBD he.symm)
  refine ⟨⟨P,?_,?_,?_,hi,rfl,rfl,incidence,?_⟩⟩
  · intro i
    rcases classified i with he | he | ht
    · exact he ▸ s.first_indec
    · exact he ▸ s.second_indec
    · exact ht.1
  · intro i
    rcases classified i with he | he | ht
    · exact he ▸ s.D_subset_first
    · exact he ▸ s.D_subset_second
    · exact ht.2.1
  · intro i
    have hrD := c.rankD
    rcases classified i with he | he | ht
    · have hr : natRank M s.F₁ + 3 = natRank M M.E := s.first_rank
      rw [he]; omega
    · have hr : natRank M s.F₂ + 3 = natRank M M.E := s.second_rank
      rw [he]; omega
    · exact ht.2.2.1
  · intro R hR hDR hrR
    rcases all R hR hDR hrR with he | he | he | he | he | he
    · exact ⟨0,he.symm⟩
    · exact ⟨3,he.symm⟩
    · exact ⟨1,he.symm⟩
    · exact ⟨4,he.symm⟩
    · exact ⟨2,he.symm⟩
    · exact ⟨5,he.symm⟩
end CountingFrame
end TutteFormalization.Homotopy
