import TutteFormalization.Homotopy.TrianglePaths
import TutteFormalization.Homotopy.OccurrenceCounts

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Source Cases 2.1.1 and 2.1.2, with the actual occurrence decrease and
containment facts required for reinsertion into the original loop. -/
theorem corankTwo_shortcut_decreases (hΓ : ModularCut M Γ) {H K L D G F : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L)
    (hF : Indecomposable M F) (hc : CorankTwo M F)
    (hFH : F ⊆ H) (hFK : F ⊆ K) (hFL : F ⊆ L)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoL : L ∉ Γ)
    (hDH : D ⊆ H) (hDL : D ⊆ L) (hGH : G ⊆ H) (hGK : ¬ G ⊆ K) :
    ∃ q : TuttePath M,
      Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl) q ∧
      q.On D ∧ outsideCount q G <
        outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl) G := by
  classical
  let t := (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl
  have htword : t.word = [H,K,L] := rfl
  by_cases he : H = L
  · subst L
    have ht : t = backtrack hH hK hHK := by
      apply TuttePath.eq_of_word_eq
      rw [htword]
      rfl
    refine ⟨TuttePath.constant H hH,?_,?_,?_⟩
    · have hn := backtrack_null hΓ hH hK hHK hoH hoK
      change Homotopic M Γ t _
      rw [ht]
      exact hn
    · intro i; exact hDH
    · change outsideCount (TuttePath.constant H hH) G < outsideCount t G
      rw [outsideCount_word,outsideCount_word,htword]
      simp [TuttePath.word,TuttePath.constant,List.ofFn_succ,hGH,hGK]
  · have hHL := tutteAdjacent_of_corankTwo hF hc hH hL he hFH hFL
    refine ⟨TuttePath.edge hH hL hHL,?_,?_,?_⟩
    · exact triangle_shortcut hΓ hH hK hL hHK hKL hHL.symm
        (elementary_null (triangle_rankTwo_elementary hΓ hc hH hK hL hHK hKL hHL.symm
          hFH hFK hFL hoH hoK hoL))
    · exact TuttePath.edge_on _ _ _ hDH hDL
    · change outsideCount (TuttePath.edge hH hL hHL) G < outsideCount t G
      rw [outsideCount_word,outsideCount_word,htword]
      simp [TuttePath.word,TuttePath.edge,List.ofFn_succ,hGH,hGK]
end TutteFormalization.Homotopy
