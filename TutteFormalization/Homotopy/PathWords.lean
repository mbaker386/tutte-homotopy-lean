import TutteFormalization.Homotopy.PathSegments

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α}

/-- Concatenation counts the common endpoint once, including zero-edge paths. -/
theorem word_concat (p q : TuttePath M) (h : p.terminus = q.origin) :
    (p.concat q h).word = p.word ++ q.word.tail := by
  apply List.ext_getElem
  · simp [word,concat]
  · intro i hi hj
    simp only [word,List.getElem_ofFn] at *
    by_cases hip : i < p.length+1
    · rw [List.getElem_append_left (by simpa [word] using hip)]
      simp only [word,List.getElem_ofFn,concat,dif_pos (show i ≤ p.length by omega)]
    · rw [List.getElem_append_right (by simpa [word] using Nat.le_of_not_gt hip)]
      simp only [word,List.length_ofFn,List.getElem_tail,List.getElem_ofFn,concat,
        dif_neg (show ¬ i ≤ p.length by omega)]
      apply congrArg q.vertex
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
end TutteFormalization.TuttePath
