import TutteFormalization.Homotopy.TriangleRankThree
import TutteFormalization.Homotopy.OccurrenceCounts

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The two triangle moves in source 2.2.1 (indecomposable L branch),
written as an equality of endpoints and two contextual homotopies. -/
theorem triangle_exchange {H K J Z : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hJ : IsHyperplane M J) (hZ : IsHyperplane M Z)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hHZ : TutteAdjacent M H Z) (hKZ : TutteAdjacent M K Z) (hZJ : TutteAdjacent M Z J)
    (h1 : Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hZ hKZ) rfl)
      (TuttePath.edge hH hZ hHZ))
    (h2 : Homotopic M Γ ((TuttePath.edge hK hZ hKZ).concat (TuttePath.edge hZ hJ hZJ) rfl)
      (TuttePath.edge hK hJ hKJ)) :
    Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl)
      ((TuttePath.edge hH hZ hHZ).concat (TuttePath.edge hZ hJ hZJ) rfl) := by
  have ha := h2.symm.prepend (TuttePath.edge hH hK hHK)
    (TuttePath.off_of_concat_left rfl h1.off.1) rfl
  have hb := h1.append (TuttePath.edge hZ hJ hZJ) (TuttePath.off_of_concat_right rfl h2.off.1) rfl
  have hb' : Homotopic M Γ
      ((TuttePath.edge hH hK hHK).concat
        ((TuttePath.edge hK hZ hKZ).concat (TuttePath.edge hZ hJ hZJ) rfl) rfl)
      ((TuttePath.edge hH hZ hHZ).concat (TuttePath.edge hZ hJ hZJ) rfl) := by
    have hh := TuttePath.concat_assoc (TuttePath.edge hH hK hHK)
      (TuttePath.edge hK hZ hKZ) (TuttePath.edge hZ hJ hZJ) rfl rfl
    exact hh ▸ hb
  exact ha.trans hb'

/-- A replacement middle hyperplane on G removes one outside occurrence;
this numerical fact is independent of the surrounding loop. -/
theorem twoEdge_count_decreases {H K J Z G : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K)
    (hJ : IsHyperplane M J) (hZ : IsHyperplane M Z)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hHZ : TutteAdjacent M H Z) (hZJ : TutteAdjacent M Z J)
    (hGZ : G ⊆ Z) (hGK : ¬ G ⊆ K) :
    outsideCount ((TuttePath.edge hH hZ hHZ).concat (TuttePath.edge hZ hJ hZJ) rfl) G <
      outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) G := by
  classical
  rw [outsideCount_word,outsideCount_word]
  change ([H,Z,J].countP (fun A => decide (¬ G ⊆ A))) <
    ([H,K,J].countP (fun A => decide (¬ G ⊆ A)))
  simp only [List.countP_cons,List.countP_nil]
  simp [hGZ,hGK]
end TutteFormalization.Homotopy
