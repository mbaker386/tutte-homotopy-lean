import TutteFormalization.Homotopy.OffJoinShortcut
import TutteFormalization.Homotopy.TwoStepEdges
import TutteFormalization.Homotopy.LocalReplacement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2.1 in the full loop, including its strict u decrease. No
non-nullness assumption or structural result is hidden in the local data. -/
theorem shorten_off_join_segment (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hlower : Lower M Γ n) (p : TuttePath M) (k : ℕ) (hk : k+2 ≤ p.length)
    {D G : Set α} (hp : p.Off Γ) (hon : p.On D) (hD : M.IsFlat D)
    (hG : Indecomposable M G) (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1)
    (hrF : natRank M (p.twoStep k hk).carrier + 3 = natRank M M.E)
    (hGH : G ⊆ p.vertex ⟨k,by omega⟩) (hGK : ¬ G ⊆ p.vertex ⟨k+1,by omega⟩)
    (hrD : natRank M M.E - natRank M D ≤ n+1)
    (hoZ : M.closure (M.closure (G ∪ (p.twoStep k hk).carrier) ∪
      (p.vertex ⟨k+1,by omega⟩ ∩ p.vertex ⟨k+2,by omega⟩)) ∉ Γ) :
    ∃ r : TuttePath M, Homotopic M Γ p r ∧ r.On D ∧ outsideCount r G < outsideCount p G := by
  let t := p.twoStep k hk
  have hHK : TutteAdjacent M (t.vertex 0) (t.vertex 1) := t.adjacent ⟨0,by change 0 < 2; decide⟩
  have hKJ : TutteAdjacent M (t.vertex 1) (t.vertex 2) := t.adjacent ⟨1,by change 1 < 2; decide⟩
  have heF : t.carrier = t.vertex 0 ∩ t.vertex 1 ∩ t.vertex 2 := p.twoStep_carrier k hk
  have hDF : D ⊆ t.carrier := (t.on_iff_subset_carrier D).mp (p.twoStep_on k hk hon)
  obtain ⟨q,hq,hqD,hcount⟩ := off_join_shortcut hM hΓ hlower
    (t.isHyperplane 0) (t.isHyperplane 1) (t.isHyperplane 2) hHK hKJ
    t.carrier_indecomposable heF hrF hD hG hDG hDF hrG hGH hGK hrD (hp _) (hp _) (hp _) hoZ
  have he := p.twoStep_eq_edges k hk
  rw [← he] at hq hcount
  exact replace_twoStep_decreases p k hk hp hon q hq hqD hcount
end TutteFormalization.Homotopy
