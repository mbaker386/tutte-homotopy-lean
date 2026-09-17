import TutteFormalization.Homotopy.Special

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α}

/-- Indices, not distinct vertices: every outside occurrence is counted. The
repeated terminal vertex contributes zero for loops based at a hyperplane on G. -/
noncomputable def outsideIndices (p : TuttePath M) (G : Set α) : Finset (Fin (p.length+1)) := by
  classical
  exact Finset.univ.filter (fun i => ¬ G ⊆ p.vertex i)
noncomputable def outsideCount (p : TuttePath M) (G : Set α) : ℕ := (outsideIndices p G).card

theorem mem_outsideIndices {p : TuttePath M} {G : Set α} {i : Fin (p.length+1)} :
    i ∈ outsideIndices p G ↔ ¬ G ⊆ p.vertex i := by
  classical
  simp only [outsideIndices,Finset.mem_filter,Finset.mem_univ,true_and]

theorem outsideCount_zero_iff (p : TuttePath M) (G : Set α) : outsideCount p G = 0 ↔ p.On G := by
  classical
  simp only [outsideCount,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem,mem_outsideIndices,not_not]
  rfl

noncomputable def firstOutside (p : TuttePath M) (G : Set α) (h : 0 < outsideCount p G) :
    Fin (p.length+1) := (outsideIndices p G).min' (Finset.card_pos.mp h)

theorem firstOutside_bad (p : TuttePath M) (G : Set α) (h : 0 < outsideCount p G) :
    ¬ G ⊆ p.vertex (firstOutside p G h) :=
  mem_outsideIndices.mp (Finset.min'_mem _ _)

theorem before_firstOutside (p : TuttePath M) (G : Set α) (h : 0 < outsideCount p G)
    {i : Fin (p.length+1)} (hi : i < firstOutside p G h) : G ⊆ p.vertex i := by
  by_contra hn
  have hle := Finset.min'_le (outsideIndices p G) i (mem_outsideIndices.mpr hn)
  exact (not_le_of_gt hi) hle

theorem firstOutside_interior (p : TuttePath M) (G : Set α) (h : 0 < outsideCount p G)
    (hclosed : Closed p) (hG : G ⊆ p.origin) :
    0 < (firstOutside p G h).val ∧ (firstOutside p G h).val < p.length := by
  have hb := firstOutside_bad p G h
  have h0 : (firstOutside p G h).val ≠ 0 := by
    intro he
    have hi : firstOutside p G h = 0 := Fin.ext he
    exact hb (hi ▸ hG)
  have hl : (firstOutside p G h).val ≠ p.length := by
    intro he
    have hi : firstOutside p G h = Fin.last p.length := Fin.ext he
    exact hb (hi ▸ (hG.trans_eq hclosed))
  have := (firstOutside p G h).isLt
  omega

/-- Total index lookup; at the first outside occurrence in a based closed
loop the predecessor and successor are interior, so no wraparound occurs. -/
def vertexMod (p : TuttePath M) (i : ℕ) : Set α :=
  p.vertex ⟨i % (p.length+1),Nat.mod_lt _ (by omega)⟩

def localTriple (p : TuttePath M) (i : ℕ) : Set α :=
  vertexMod p (i-1) ∩ vertexMod p i ∩ vertexMod p (i+1)

noncomputable def firstTripleCorank (p : TuttePath M) (G : Set α) : ℕ := by
  classical
  exact if h : 0 < outsideCount p G then
    natRank M M.E - natRank M (localTriple p (firstOutside p G h).val) else 0

/-- Minimize attained natural values successively. No finiteness of the set
of paths is asserted or required. -/
theorem exists_lex_min_measure {β : Type*} (S : β → Prop) (u v : β → ℕ)
    (hne : ∃ x, S x) :
    ∃ x, S x ∧ (∀ y, S y → u x ≤ u y) ∧ (∀ y, S y → u x = u y → v x ≤ v y) := by
  classical
  have hu : ∃ n, ∃ x, S x ∧ u x = n := by obtain ⟨x,hx⟩ := hne; exact ⟨u x,x,hx,rfl⟩
  obtain ⟨x,hx,hux⟩ := Nat.find_spec hu
  have hv : ∃ n, ∃ y, S y ∧ u y = Nat.find hu ∧ v y = n := ⟨v x,x,hx,hux,rfl⟩
  obtain ⟨z,hz,huz,hvz⟩ := Nat.find_spec hv
  refine ⟨z,hz,?_,?_⟩
  · intro y hy
    rw [huz]
    exact Nat.find_min' hu ⟨y,hy,rfl⟩
  · intro y hy he
    rw [hvz]
    exact Nat.find_min' hv ⟨y,hy,he.symm.trans huz,rfl⟩
end TutteFormalization.Homotopy
