import TutteFormalization.Homotopy.CorankTwoShortcut
import TutteFormalization.Homotopy.LocalReplacement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Source Case 2.1 applied inside the actual loop. The middle occurrence
is removed, while the fixed contexts retain all their vertex occurrences. -/
theorem shorten_corankTwo_segment (hΓ : ModularCut M Γ) (p : TuttePath M)
    (k : ℕ) (hk : k+2 ≤ p.length) {D G : Set α} (hp : p.Off Γ) (hon : p.On D)
    (hc : CorankTwo M (p.twoStep k hk).carrier)
    (hG : G ⊆ p.vertex ⟨k,by omega⟩) (hbad : ¬ G ⊆ p.vertex ⟨k+1,by omega⟩) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let t := p.twoStep k hk
  let H := t.vertex 0
  let K := t.vertex 1
  let L := t.vertex 2
  have hHK : TutteAdjacent M H K := t.adjacent ⟨0,by change 0 < 2; decide⟩
  have hKL : TutteAdjacent M K L := t.adjacent ⟨1,by change 1 < 2; decide⟩
  have he : (TuttePath.edge (t.isHyperplane 0) (t.isHyperplane 1) hHK).concat
      (TuttePath.edge (t.isHyperplane 1) (t.isHyperplane 2) hKL) rfl = t := by
    apply TuttePath.ext_vertices (p := (TuttePath.edge (t.isHyperplane 0) (t.isHyperplane 1) hHK).concat
      (TuttePath.edge (t.isHyperplane 1) (t.isHyperplane 2) hKL) rfl) (q := t) rfl
    intro i; fin_cases i <;> rfl
  have hsub (i : Fin 3) : t.carrier ⊆ t.vertex i := by
    intro x hx; exact Set.mem_iInter.mp hx i
  obtain ⟨q,hq,hqD,hcount⟩ := corankTwo_shortcut_decreases hΓ
    (t.isHyperplane 0) (t.isHyperplane 1) (t.isHyperplane 2) hHK hKL
    t.carrier_indecomposable hc (hsub 0) (hsub 1) (hsub 2)
    (hp _) (hp _) (hp _) (hon _) (hon _) hG hbad
  rw [he] at hq hcount
  exact replace_twoStep_decreases p k hk hp hon q hq hqD hcount
end TutteFormalization.Homotopy
