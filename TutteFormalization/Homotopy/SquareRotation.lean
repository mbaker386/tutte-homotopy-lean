import TutteFormalization.Homotopy.PathSegments

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α}

/-- A literal four-edge word can be rotated halfway through using two valid
segments, so no new elementary move is needed for fourth-kind recognition. -/
theorem square_rotation {p : TuttePath M} {A X B Y : Set α}
    (hw : p.word = [A,X,B,Y,A]) :
    ∃ a b : TuttePath M, ∃ hab : a.terminus = b.origin,
      ∃ hba : b.terminus = a.origin, p = a.concat b hab ∧
        (b.concat a hba).word = [B,Y,A,X,B] := by
  have hp : p.length = 4 := by
    have h := congrArg List.length hw
    simpa [TuttePath.word] using h
  have hv : ∀ i : Fin 5, p.vertex ⟨i.val,by omega⟩ = ![A,X,B,Y,A] i := by
    intro i
    have h := congrArg (fun xs : List (Set α) => xs[i.val]?) hw
    simp only [TuttePath.word,List.getElem?_ofFn] at h
    fin_cases i <;> simpa [hp] using h
  have hc : Closed p := by
    change p.vertex 0 = p.vertex (Fin.last p.length)
    have h0 := hv 0
    have h4 := hv 4
    exact (h0.trans h4.symm).trans (congrArg p.vertex (Fin.ext (by simpa using hp.symm)))
  let a := p.initialSegment 2 (by omega)
  let b := p.finalSegment 2 (by omega)
  have hab : a.terminus = b.origin := rfl
  have hba : b.terminus = a.origin := by
    simpa [a,b] using hc.symm
  refine ⟨a,b,hab,hba,p.split_at 2 (by omega),?_⟩
  apply List.ext_getElem
  · simp [TuttePath.word,a,b,TuttePath.concat,TuttePath.initialSegment,TuttePath.finalSegment,hp]
  · intro i hi hj
    have hib : i < 5 := by simpa using hj
    simp only [TuttePath.word,List.getElem_ofFn]
    interval_cases i <;>
      simp [a,b,TuttePath.concat,TuttePath.initialSegment,TuttePath.finalSegment,hp] <;>
      first | exact hv 0 | exact hv 1 | exact hv 2 | exact hv 3 | exact hv 4
end TutteFormalization.Homotopy
