import TutteFormalization.Homotopy.OccurrenceMeasures

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

/-- The literal two-edge segment beginning at index k. -/
def twoStep (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length) : TuttePath M where
  length := 2
  vertex i := p.vertex ⟨k+i.val,by omega⟩
  isHyperplane i := p.isHyperplane _
  adjacent i := p.adjacent ⟨k+i.val,by omega⟩

theorem twoStep_carrier (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length) :
    (p.twoStep k hk).carrier =
      p.vertex ⟨k,by omega⟩ ∩ p.vertex ⟨k+1,by omega⟩ ∩ p.vertex ⟨k+2,by omega⟩ := by
  ext x
  simp only [carrier,twoStep,Set.mem_iInter,Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨⟨h 0,h 1⟩,h 2⟩
  · rintro ⟨⟨h0,h1⟩,h2⟩ i
    fin_cases i <;> assumption
end TutteFormalization.TuttePath

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α}

theorem vertexMod_eq (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length) :
    vertexMod p k = p.vertex ⟨k,by omega⟩ := by
  unfold vertexMod
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by omega)

theorem localTriple_indec [M.Finite] (p : TuttePath M) (i : ℕ) (hi : 0 < i) (hil : i < p.length) :
    Indecomposable M (localTriple p i) := by
  have hh := (p.twoStep (i-1) (by omega)).carrier_indecomposable
  rw [TuttePath.twoStep_carrier] at hh
  have h1 : i-1+1 = i := by omega
  have h2 : i-1+2 = i+1 := by omega
  simpa only [localTriple,vertexMod_eq p (i-1) (by omega),vertexMod_eq p i (by omega),
    vertexMod_eq p (i+1) (by omega),h1,h2] using hh

theorem carrier_subset_localTriple (p : TuttePath M) (i : ℕ) : p.carrier ⊆ localTriple p i := by
  intro x hx
  exact ⟨⟨Set.mem_iInter.mp hx _,Set.mem_iInter.mp hx _⟩,Set.mem_iInter.mp hx _⟩

theorem on_localTriple (p : TuttePath M) {D : Set α} (h : p.On D) (i : ℕ) : D ⊆ localTriple p i := by
  intro x hx
  exact ⟨⟨h _ hx,h _ hx⟩,h _ hx⟩

theorem localTriple_corank_ge_two [M.Finite] (p : TuttePath M) (i : ℕ)
    (hi : 0 < i) (hil : i < p.length) :
    2 ≤ natRank M M.E - natRank M (localTriple p i) := by
  have hadj := p.adjacent ⟨i-1,by omega⟩
  have hr := corankTwo_natRank hadj.2.2
  have h1 : i-1+1 = i := by omega
  have hsub : localTriple p i ⊆
      p.vertex (⟨i-1,by omega⟩ : Fin p.length).castSucc ∩
        p.vertex (⟨i-1,by omega⟩ : Fin p.length).succ := by
    simp only [localTriple,vertexMod_eq p (i-1) (by omega),vertexMod_eq p i (by omega),
      Fin.castSucc_mk,Fin.succ_mk,h1]
    exact Set.inter_subset_left
  have hm := natRank_mono (M := M) hsub
  omega

theorem firstTriple_bounds [M.Finite] (p : TuttePath M) (G : Set α)
    (h : 0 < outsideCount p G) (hclosed : Closed p) (hG : G ⊆ p.origin) :
    2 ≤ firstTripleCorank p G ∧
      firstTripleCorank p G ≤ natRank M M.E - natRank M p.carrier := by
  have hi := firstOutside_interior p G h hclosed hG
  have hlo := localTriple_corank_ge_two p (firstOutside p G h).val hi.1 hi.2
  have hm := natRank_mono (M := M) (carrier_subset_localTriple p (firstOutside p G h).val)
  simp only [firstTripleCorank,dif_pos h]
  omega
end TutteFormalization.Homotopy
