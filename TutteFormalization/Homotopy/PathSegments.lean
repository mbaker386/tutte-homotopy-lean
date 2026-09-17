import TutteFormalization.Homotopy.Carrier

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

/-- The suffix starting at vertex k, including that shared vertex once. -/
def finalSegment (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length) : TuttePath M where
  length := p.length - k
  vertex i := p.vertex ⟨k+i.val,by omega⟩
  isHyperplane i := p.isHyperplane _
  adjacent i := p.adjacent ⟨k+i.val,by omega⟩

theorem initial_final_endpoints (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length) :
    (p.initialSegment k hk).terminus = (p.finalSegment k hk).origin := rfl

theorem split_at (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length) :
    p = (p.initialSegment k hk).concat (p.finalSegment k hk)
      (p.initial_final_endpoints k hk) := by
  apply ext_vertices (by simp only [concat,initialSegment,finalSegment]; omega)
  intro i
  simp only [concat,initialSegment,finalSegment,Fin.cast]
  split_ifs with hi
  · rfl
  · apply congrArg p.vertex
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

theorem initialSegment_off (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length)
    {Γ : Set (Set α)} (h : p.Off Γ) : (p.initialSegment k hk).Off Γ := fun i => h _

theorem finalSegment_off (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length)
    {Γ : Set (Set α)} (h : p.Off Γ) : (p.finalSegment k hk).Off Γ := fun i => h _

@[simp] theorem finalSegment_terminus (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length) :
    (p.finalSegment k hk).terminus = p.terminus := by
  apply congrArg p.vertex
  apply Fin.ext
  change k + (p.length - k) = p.length
  omega

/-- Vertex words determine actual paths, including the zero-edge case. -/
theorem eq_of_word_eq {p q : TuttePath M} (h : p.word = q.word) : p = q := by
  have hl : p.length = q.length := by
    have := congrArg List.length h
    simp only [word,List.length_ofFn] at this
    omega
  apply ext_vertices hl
  intro i
  have hi := congrArg (fun xs : List (Set α) => xs[i.val]?) h
  simp only [word, List.getElem?_ofFn] at hi
  simpa only [dif_pos i.isLt, dif_pos (show i.val < q.length + 1 by omega),
    Option.some.injEq, Fin.cast, Fin.eta] using hi
theorem off_of_mem_word {p : TuttePath M} {Γ : Set (Set α)} (h : p.Off Γ)
    {H : Set α} (hm : H ∈ p.word) : H ∉ Γ := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
  exact h i
end TutteFormalization.TuttePath
