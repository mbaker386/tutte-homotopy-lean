import TutteFormalization.Homotopy.Backtrack
import TutteFormalization.Homotopy.Reversal

namespace TutteFormalization
variable {α : Type*} {M : Matroid α}
namespace TuttePath

def initialSegment (p : TuttePath M) (n : ℕ) (hn : n ≤ p.length) : TuttePath M where
  length := n
  vertex i := p.vertex ⟨i.val, by omega⟩
  isHyperplane i := p.isHyperplane _
  adjacent i := p.adjacent ⟨i.val, by omega⟩

def edge {H K : Set α} (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (h : TutteAdjacent M H K) : TuttePath M where
  length := 1
  vertex := ![H,K]
  isHyperplane i := by fin_cases i <;> assumption
  adjacent i := by fin_cases i; exact h

@[simp] theorem initialSegment_origin (p : TuttePath M) (n) (hn) : (p.initialSegment n hn).origin = p.origin := rfl

theorem split_last (p : TuttePath M) (n : ℕ) (hp : p.length = n + 1) :
    ∃ a e : TuttePath M, a.length = n ∧ e.length = 1 ∧
      ∃ h : a.terminus = e.origin, p = a.concat e h := by
  let a := p.initialSegment n (by omega)
  let e := edge (p.isHyperplane ⟨n, by omega⟩) (p.isHyperplane ⟨n+1, by omega⟩)
    (p.adjacent ⟨n, by omega⟩)
  refine ⟨a, e, rfl, rfl, rfl, ?_⟩
  apply ext_vertices hp
  intro i
  by_cases hi : i.val ≤ n
  · simp only [a, e, concat, initialSegment, edge, Fin.cast, Fin.val_mk, hi, ↓reduceDIte]
  · have hi' : i.val = n + 1 := by have := i.isLt; omega
    simp [a, e, concat, initialSegment, edge, Fin.cast, hi, hi']
    exact congrArg p.vertex (Fin.ext hi')

theorem off_of_concat_left {p q : TuttePath M} {Γ : Set (Set α)}
    (h : p.terminus = q.origin) (hoff : (p.concat q h).Off Γ) : p.Off Γ := by
  intro i
  have ho := hoff ⟨i.val, by have := i.isLt; change i.val < p.length + q.length + 1; omega⟩
  simpa [concat, show i.val ≤ p.length by omega] using ho

theorem off_of_concat_right {p q : TuttePath M} {Γ : Set (Set α)}
    (h : p.terminus = q.origin) (hoff : (p.concat q h).Off Γ) : q.Off Γ := by
  intro i
  have ho := hoff ⟨p.length + i.val, by have := i.isLt; change p.length + i.val < p.length + q.length + 1; omega⟩
  by_cases hi : i.val = 0
  · have hv : q.vertex i = q.origin := congrArg q.vertex (Fin.ext hi)
    rw [hv, ← h]
    simpa [concat, hi, terminus, Fin.last] using ho
  · simpa [concat, show ¬ p.length + i.val ≤ p.length by omega] using ho
end TuttePath
namespace Homotopy
variable [M.Finite] {Γ : Set (Set α)}

theorem one_edge_cancel (hΓ : ModularCut M Γ) (p : TuttePath M) (hp : p.length = 1)
    (hoff : p.Off Γ) : NullHomotopic M Γ (p.concat p.reverse (by simp)) := by
  have hedge : TutteAdjacent M p.origin p.terminus := by
    simpa [TuttePath.origin, TuttePath.terminus, Fin.last, hp] using
      p.adjacent ⟨0, by omega⟩
  have heq : p.concat p.reverse (by simp) =
      backtrack (p.isHyperplane 0) (p.isHyperplane (Fin.last p.length)) hedge := by
    apply TuttePath.ext_vertices (by change p.length + p.length = 2; omega)
    intro i
    have hi : i.val < 3 := by have := i.isLt; change i.val < p.length + p.length + 1 at this; omega
    interval_cases hv : i.val <;>
      simp [TuttePath.concat, TuttePath.reverse, backtrack, hp, hv,
        Fin.cast, Fin.rev, TuttePath.origin, TuttePath.terminus, Fin.last]
  rw [heq]
  exact backtrack_null hΓ _ _ hedge (hoff 0) (hoff (Fin.last p.length))
theorem reverse_cancel (hΓ : ModularCut M Γ) (p : TuttePath M) (hoff : p.Off Γ) :
    NullHomotopic M Γ (p.concat p.reverse (by simp)) := by
  suffices ∀ n, ∀ q : TuttePath M, q.length = n → q.Off Γ →
      NullHomotopic M Γ (q.concat q.reverse (by simp)) from this p.length p rfl hoff
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hq hOff
    cases n with
    | zero =>
      have heq : q = TuttePath.constant q.origin (q.isHyperplane 0) := by
        apply TuttePath.ext_vertices hq
        intro i
        exact congrArg q.vertex (Fin.ext (by have := i.isLt; omega))
      rw [heq]
      have hc := constant_null q.origin (q.isHyperplane 0) (hOff 0)
      simpa only [TuttePath.reverse_constant q.origin (q.isHyperplane 0),
        TuttePath.concat_constant_eq (TuttePath.constant q.origin (q.isHyperplane 0))
          q.origin (q.isHyperplane 0) rfl] using hc
    | succ k =>
      obtain ⟨a, e, ha, he, hae, rfl⟩ := q.split_last k hq
      have hoa := TuttePath.off_of_concat_left hae hOff
      have hoe := TuttePath.off_of_concat_right hae hOff
      have hsmall := ih k (by omega) a ha hoa
      have hedge := one_edge_cancel hΓ e he hoe
      have hee : e.terminus = e.reverse.origin := by simp
      have haa : a.terminus = a.reverse.origin := by simp
      have hea : e.reverse.terminus = a.reverse.origin := by simpa using hae.symm
      have hc := null_context hedge ((off_cutPlus a).mpr hoa)
        (TuttePath.reverse_off ((off_cutPlus a).mpr hoa)) haa (by simpa using hae)
      have hc' : Homotopic M Γ
          ((a.concat e hae).concat (a.concat e hae).reverse (by simp))
          (a.concat a.reverse haa) := by
        simpa only [insertLoop, TuttePath.reverse_concat a e hae,
          TuttePath.concat_assoc a e (e.reverse.concat a.reverse hea) hae (by simp),
          TuttePath.concat_assoc a (e.concat e.reverse hee) a.reverse (by simpa using hae)
            (by simpa using hea),
          TuttePath.concat_assoc e e.reverse a.reverse hee hea] using hc
      exact hc'.trans hsmall
end Homotopy
end TutteFormalization
