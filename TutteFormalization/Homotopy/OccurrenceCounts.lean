import TutteFormalization.Homotopy.OccurrenceMeasures
import TutteFormalization.Homotopy.PathWords

namespace TutteFormalization.Homotopy
open Classical
variable {α : Type*} {M : Matroid α}

private theorem countP_ofFn_sum {β : Type*} (P : β → Bool) {n : ℕ} (f : Fin n → β) :
    (List.ofFn f).countP P = ∑ i : Fin n, if P (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
    omega

/-- The occurrence measure agrees with counting the actual vertex word. -/
theorem outsideCount_word (p : TuttePath M) (G : Set α) :
    outsideCount p G = p.word.countP (fun H => decide (¬ G ⊆ H)) := by
  classical
  rw [TuttePath.word,countP_ofFn_sum]
  simp only [Bool.decide_iff,Finset.sum_boole,outsideCount,outsideIndices,Nat.cast_id]

/-- Gluing counts the common vertex once. This identity makes local path
replacement comparisons independent of their two surrounding contexts. -/
theorem outsideCount_concat (p q : TuttePath M) (h : p.terminus = q.origin) (G : Set α) :
    outsideCount (p.concat q h) G + (if G ⊆ q.origin then 0 else 1) =
      outsideCount p G + outsideCount q G := by
  classical
  rw [outsideCount_word,outsideCount_word,outsideCount_word,TuttePath.word_concat,List.countP_append]
  have hq : q.word = q.origin :: q.word.tail := by
    unfold TuttePath.word TuttePath.origin
    rw [List.ofFn_succ]
    rfl
  conv_rhs => rw [hq,List.countP_cons]
  by_cases hg : G ⊆ q.origin <;> simp [hg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
end TutteFormalization.Homotopy
