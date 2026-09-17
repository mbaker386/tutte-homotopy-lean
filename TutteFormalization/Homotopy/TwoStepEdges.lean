import TutteFormalization.Homotopy.SegmentContexts

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

/-- The literal two-edge segment agrees with the concatenation used by the
local deformation lemmas; no vertices are dropped by this identification. -/
theorem twoStep_eq_edges (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length) :
    let t := p.twoStep k hk
    t = (edge (t.isHyperplane 0) (t.isHyperplane 1)
      (t.adjacent ⟨0,by change 0 < 2; decide⟩)).concat
      (edge (t.isHyperplane 1) (t.isHyperplane 2) (t.adjacent ⟨1,by change 1 < 2; decide⟩)) rfl := by
  dsimp only
  apply eq_of_word_eq
  rfl
end TutteFormalization.TuttePath
