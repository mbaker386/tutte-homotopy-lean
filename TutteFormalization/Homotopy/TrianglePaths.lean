import TutteFormalization.Homotopy.RankTwoPencilModel
import TutteFormalization.Homotopy.TopCutRecognition
import TutteFormalization.Homotopy.LowerCalculus

namespace TutteFormalization.TuttePath
variable {α : Type*} {M : Matroid α} {H K L : Set α}
def triangle (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L) (hLH : TutteAdjacent M L H) : TuttePath M where
  length := 3
  vertex := ![H,K,L,H]
  isHyperplane i := by fin_cases i <;> assumption
  adjacent i := by fin_cases i <;> assumption

theorem triangle_word (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L) (hLH : TutteAdjacent M L H) :
    (triangle hH hK hL hHK hKL hLH).word = [H,K,L,H] := rfl

theorem triangle_off {Γ : Set (Set α)} (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hL : IsHyperplane M L) (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L)
    (hLH : TutteAdjacent M L H) (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoL : L ∉ Γ) :
    (triangle hH hK hL hHK hKL hLH).Off Γ := by
  intro i; fin_cases i <;> assumption
end TutteFormalization.TuttePath

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D H K L : Set α}

/-- Source Case 2.1.2: the actual triangle on a corank-two flat is second kind. -/
theorem triangle_rankTwo_elementary (hΓ : ModularCut M Γ) (hD : CorankTwo M D)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L) (hLH : TutteAdjacent M L H)
    (hDH : D ⊆ H) (hDK : D ⊆ K) (hDL : D ⊆ L)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoL : L ∉ Γ) :
    Elementary M Γ (TuttePath.triangle hH hK hL hHK hKL hLH) := by
  let P : Fin 3 → Set α := ![H,K,L]
  have hp : ∀ i, IsHyperplane M (P i) := by intro i; fin_cases i <;> assumption
  have hd : ∀ i, D ⊆ P i := by intro i; fin_cases i <;> assumption
  have hi : Function.Injective P := by
    intro i j he
    fin_cases i <;> fin_cases j <;> dsimp [P] at he
    all_goals first
      | rfl
      | exact False.elim (hHK.1 he)
      | exact False.elim (hHK.1 he.symm)
      | exact False.elim (hKL.1 he)
      | exact False.elim (hKL.1 he.symm)
      | exact False.elim (hLH.1 he)
      | exact False.elim (hLH.1 he.symm)
  obtain ⟨φ,_,hφ⟩ := exists_rankTwoPencilEmbedding hD P hp hd hi
  have hoff : ∀ i, φ.image {i} ∉ cutPlus M Γ := by
    intro i; rw [hφ]
    fin_cases i
    · exact (hyperplane_off_cutPlus hH).mpr hoH
    · exact (hyperplane_off_cutPlus hK).mpr hoK
    · exact (hyperplane_off_cutPlus hL).mpr hoL
  have cover : ∀ F, u23.Flat F → F ≠ Finset.univ → ∃ i : Fin 3, F ⊆ {i} := by decide
  have hcut := exactTopCut_of_cover φ hΓ (fun i : Fin 3 => {i}) (fun i => (u23_simple.2 i).1) hoff cover
  refine Elementary.base (BaseElementary.secondA φ _ hcut ?_ rfl
    ((off_cutPlus _).mpr (TuttePath.triangle_off hH hK hL hHK hKL hLH hoH hoK hoL)))
  rw [TuttePath.triangle_word]
  simp only [List.map_cons,List.map_nil,hφ]
  rfl

/-- A null triangle gives the literal two-edge shortcut, using only the
approved generated homotopy and reverse cancellation. -/
theorem triangle_shortcut (hΓ : ModularCut M Γ)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hL : IsHyperplane M L)
    (hHK : TutteAdjacent M H K) (hKL : TutteAdjacent M K L) (hLH : TutteAdjacent M L H)
    (hn : NullHomotopic M Γ (TuttePath.triangle hH hK hL hHK hKL hLH)) :
    Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl)
      (TuttePath.edge hH hL hLH.symm) := by
  apply homotopic_of_null_comparison hΓ
    (p := (TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl)
    (q := TuttePath.edge hH hL hLH.symm) rfl rfl
  have he : ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl).concat
      (TuttePath.edge hH hL hLH.symm).reverse rfl = TuttePath.triangle hH hK hL hHK hKL hLH := by
    apply TuttePath.ext_vertices
      (p := ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hL hKL) rfl).concat
        (TuttePath.edge hH hL hLH.symm).reverse rfl)
      (q := TuttePath.triangle hH hK hL hHK hKL hLH) rfl
    intro i; fin_cases i <;> rfl
  exact he.symm ▸ hn
end TutteFormalization.Homotopy
