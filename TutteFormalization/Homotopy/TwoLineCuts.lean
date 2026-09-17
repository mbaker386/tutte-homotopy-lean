import TutteFormalization.Homotopy.TwoLines

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.27's final count. Distinct lines on W give distinct cut hyperplanes;
every cut hyperplane is recovered from its indecomposable trace on W. -/
theorem two_cut_of_two_lines (hΓ : ModularCut M Γ) {P W Y L K : Set α}
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y) (hWY : W ≠ Y)
    (hoW : W ∉ Γ) (hoY : Y ∉ Γ) (hPW : P ⊆ W) (hPY : P ⊆ Y)
    (hc : CorankTwo M (W ∩ Y)) (hdec : ¬ Indecomposable M (W ∩ Y))
    (hcL : CorankTwo M L) (hcK : CorankTwo M K)
    (hPL : P ⊆ L) (hPK : P ⊆ K) (hLW : L ⊆ W) (hKW : K ⊆ W) (hLK : L ≠ K)
    (all : ∀ J, Indecomposable M J → CorankTwo M J → P ⊆ J → J ⊆ W → J = L ∨ J = K)
    (countL : ThreePencil M Γ L W) (countK : ThreePencil M Γ K W) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ P ⊆ U ∧ P ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → P ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  obtain ⟨U,_,hU,_,hLU,_,hUW,_,_,hiU,_,_⟩ := countL
  obtain ⟨V,_,hV,_,hKV,_,hVW,_,_,hiV,_,_⟩ := countK
  have hu : U ∩ W = L := hyperplane_inter_eq_of_corankTwo hcL hU hW hUW hLU hLW
  have hv : V ∩ W = K := hyperplane_inter_eq_of_corankTwo hcK hV hW hVW hKV hKW
  have hUV : U ≠ V := fun he => hLK (hu.symm.trans ((congrArg (fun Z => Z ∩ W) he).trans hv))
  refine ⟨U,V,hU,hV,hPL.trans hLU,hPK.trans hKV,hiU,hiV,hUV,?_⟩
  intro J hJ hPJ hiJ
  have hed := third_hyperplane_adjacent hP hrP hc hdec (Set.subset_inter hPW hPY)
    hW hY hWY Set.inter_subset_left Set.inter_subset_right hJ
    (fun he => hoW (he ▸ hiJ)) (fun he => hoY (he ▸ hiJ)) hPJ
  rcases all (J ∩ W) hed.1.2.1 hed.1.2.2 (Set.subset_inter hPJ hPW) Set.inter_subset_right with he | he
  · exact Or.inl (cut_hyperplanes_unique_above hΓ hcL hW hLW hoW hJ hU
      (he ▸ Set.inter_subset_left) hLU hiJ hiU)
  · exact Or.inr (cut_hyperplanes_unique_above hΓ hcK hW hKW hoW hJ hV
      (he ▸ Set.inter_subset_left) hKV hiJ hiV)
end TutteFormalization.Homotopy
