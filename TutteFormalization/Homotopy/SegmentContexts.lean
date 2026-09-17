import TutteFormalization.Homotopy.LocalTriple
import TutteFormalization.Homotopy.PathSegments

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

theorem initialSegment_on (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length)
    {D : Set α} (h : p.On D) : (p.initialSegment k hk).On D := fun i => h _

theorem finalSegment_on (p : TuttePath M) (k : ℕ) (hk : k ≤ p.length)
    {D : Set α} (h : p.On D) : (p.finalSegment k hk).On D := fun i => h _

theorem twoStep_on (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {D : Set α} (h : p.On D) : (p.twoStep k hk).On D := fun i => h _

theorem twoStep_off (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {Γ : Set (Set α)} (h : p.Off Γ) : (p.twoStep k hk).Off Γ := fun i => h _

/-- Isolate a literal two-edge segment with both endpoint occurrences shared
once with their contexts. All three pieces retain containment and Off facts. -/
theorem split_twoStep (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length) :
    p = (p.initialSegment k (by omega)).concat
      ((p.twoStep k hk).concat (p.finalSegment (k+2) hk) rfl) rfl := by
  apply ext_vertices (p := p)
    (q := (p.initialSegment k (by omega)).concat
      ((p.twoStep k hk).concat (p.finalSegment (k+2) hk) rfl) rfl)
    (by change p.length = k + (2 + (p.length - (k+2))); omega)
  intro i
  simp only [concat,initialSegment,twoStep,finalSegment,Fin.cast]
  split_ifs with h1 h2
  · rfl
  · apply congrArg p.vertex; apply Fin.ext; simp only [Fin.val_mk]; omega
  · apply congrArg p.vertex; apply Fin.ext; simp only [Fin.val_mk]; omega
end TutteFormalization.TuttePath
