import TutteFormalization.Homotopy.CutJoinGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Once U,V have been constructed in 2.2.2, the three hyperplanes H,Z,V
above L prove L indecomposable. All additional edges follow from the actual
corank-two flats, rather than being assumed in a path constructor. -/
theorem cut_branch_edges {A L P H K J Z U V : Set α}
    (hA : Indecomposable M A) (hcA : CorankTwo M A) (hAH : A ⊆ H) (hAK : A ⊆ K) (hAU : A ⊆ U)
    (hcL : CorankTwo M L) (hLH : L ⊆ H) (hLZ : L ⊆ Z) (hLV : L ⊆ V)
    (hP : Indecomposable M P) (hcP : CorankTwo M P) (hPJ : P ⊆ J) (hPU : P ⊆ U) (hPV : P ⊆ V)
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hZ : IsHyperplane M Z) (hU : IsHyperplane M U) (hV : IsHyperplane M V)
    (hHZ : H ≠ Z) (hVH : V ≠ H) (hVZ : V ≠ Z)
    (hUH : U ≠ H) (hUK : U ≠ K) (hUJ : U ≠ J) (hUV : U ≠ V) (hVJ : V ≠ J) :
    Indecomposable M L ∧ TutteAdjacent M H U ∧ TutteAdjacent M K U ∧
      TutteAdjacent M U J ∧ TutteAdjacent M U V ∧ TutteAdjacent M V J ∧ TutteAdjacent M V H := by
  have hiL : Indecomposable M L := (corankTwo_indecomposable_iff_three hcL).mpr
    ⟨H,Z,V,hH,hZ,hV,hHZ,hVH.symm,hVZ.symm,hLH,hLZ,hLV⟩
  exact ⟨hiL,tutteAdjacent_of_corankTwo hA hcA hH hU hUH.symm hAH hAU,
    tutteAdjacent_of_corankTwo hA hcA hK hU hUK.symm hAK hAU,
    tutteAdjacent_of_corankTwo hP hcP hU hJ hUJ hPU hPJ,
    tutteAdjacent_of_corankTwo hP hcP hU hV hUV hPU hPV,
    tutteAdjacent_of_corankTwo hP hcP hV hJ hVJ hPV hPJ,
    tutteAdjacent_of_corankTwo hiL hcL hV hH hVH hLV hLH⟩
end TutteFormalization.Homotopy
