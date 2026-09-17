import TutteFormalization.Homotopy.B2Separation
import TutteFormalization.IndecomposableComplement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- B.2's first paragraph: maximal indecomposable P below L rules out another
 decomposable corank-two flat between P and either endpoint hyperplane. -/
theorem unique_decomposable_below_endpoint {P L X Y : Set α}
    (hP : Indecomposable M P) (hL : CorankTwo M L) (hPL : P ⊆ L)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hLX : L ⊆ X) (hLY : L ⊆ Y)
    (maximal : ∀ V, Indecomposable M V → P ⊆ V → V ⊆ L → natRank M V ≤ natRank M P) :
    ∀ I, CorankTwo M I → ¬ Indecomposable M I → P ⊆ I → I ⊆ X → I = L := by
  intro I hI hnI hPI hIX
  by_contra hIL
  have hILr := corankTwo_natRank hL
  have hIIr := corankTwo_natRank hI
  have hXYL := hyperplane_inter_eq_of_corankTwo hL hX hY hXY hLX hLY
  have hnIY : ¬ I ⊆ Y := by
    intro hIY
    have hsub : I ⊆ L := (Set.subset_inter hIX hIY).trans_eq hXYL
    exact hIL (flat_eq_of_subset_of_natRank_le hI.1 hL.1 hsub (by omega))
  have hj : M.closure (Y ∪ I) = M.E := by
    have hYJ : Y ⊆ M.closure (Y ∪ I) :=
      M.subset_closure_of_subset' Set.subset_union_left hY.1.subset_ground
    rcases hY.2.2 _ (M.isFlat_closure _) hYJ with heq | heq
    · exact False.elim (hnIY ((M.subset_closure_of_subset' Set.subset_union_right
        hI.1.subset_ground).trans_eq heq))
    · exact heq
  obtain ⟨U,hU,hPU,hUY,hUI,hUr⟩ := exists_indecomposable_complement
    (hyperplane_indecomposable hY) hP hI.1 (hPL.trans hLY) hPI hj
  have hrUE := natRank_mono (M := M) hU.1.subset_ground
  have hrPI := natRank_mono (M := M) hPI
  have hUr' : natRank M U = natRank M P + 2 := by omega
  have hj' : M.closure (I ∪ U) = M.E := by simpa only [Set.union_comm] using hUI
  have hi := corankTwo_inter_eq_of_join_eq_ground hP.1 hI hU.1 hPI hPU hUr' hj'
  obtain ⟨V,W,hV,hW,hPV,hPW,hVU,hWU,hVW,hVr,hWr⟩ :=
    exists_indecomposable_diamond hU hP hPU hUr'
  have hPV' : P ⊂ V := Set.ssubset_iff_subset_ne.mpr ⟨hPV,by
    intro h; have := congrArg (natRank M) h; omega⟩
  have hPW' : P ⊂ W := Set.ssubset_iff_subset_ne.mpr ⟨hPW,by
    intro h; have := congrArg (natRank M) h; omega⟩
  obtain ⟨hHV,hiV⟩ := diamond_join_inter hU.1 hI hV.1 hi hPV' hVU hUr' hVr hj'
  obtain ⟨hHW,hiW⟩ := diamond_join_inter hU.1 hI hW.1 hi hPW' hWU hUr' hWr hj'
  have hne : M.closure (I ∪ V) ≠ M.closure (I ∪ W) := by
    intro h
    exact hVW (hiV.symm.trans ((congrArg (fun H => U ∩ H) h).trans hiW))
  have hIV : I ⊆ M.closure (I ∪ V) :=
    M.subset_closure_of_subset' Set.subset_union_left hI.1.subset_ground
  have hIW : I ⊆ M.closure (I ∪ W) :=
    M.subset_closure_of_subset' Set.subset_union_left hI.1.subset_ground
  have hmeet := hyperplane_inter_eq_of_corankTwo hI hHV hHW hne hIV hIW
  have hdec : ¬ Indecomposable M (M.closure (I ∪ V) ∩ M.closure (I ∪ W)) := by
    simpa only [hmeet] using hnI
  rcases (separation_hyperplanes hHV hHW hdec).2 X hX (by simpa only [hmeet] using hIX) with hx | hx
  · have hVX : V ⊆ X := (M.subset_closure_of_subset' Set.subset_union_right
        hV.1.subset_ground).trans_eq hx.symm
    have hVL : V ⊆ L := (Set.subset_inter hVX (hVU.trans hUY)).trans_eq hXYL
    have := maximal V hV hPV hVL
    omega
  · have hWX : W ⊆ X := (M.subset_closure_of_subset' Set.subset_union_right
        hW.1.subset_ground).trans_eq hx.symm
    have hWL : W ⊆ L := (Set.subset_inter hWX (hWU.trans hUY)).trans_eq hXYL
    have := maximal W hW hPW hWL
    omega

/-- B.2, with the approved HD-004 repair: an indecomposable flat below a
 decomposable corank-two flat extends to an indecomposable corank-three flat. -/
theorem exists_indecomposable_corankThree {S L : Set α}
    (hS : Indecomposable M S) (hL : CorankTwo M L)
    (hnL : ¬ Indecomposable M L) (hSL : S ⊆ L) :
    ∃ P, Indecomposable M P ∧ S ⊆ P ∧ P ⊂ L ∧ natRank M P + 3 = natRank M M.E := by
  let C : Set (Set α) := {P | Indecomposable M P ∧ S ⊆ P ∧ P ⊆ L}
  have hCfin : C.Finite := M.ground_finite.powerset.subset (fun _ h => h.1.1.subset_ground)
  obtain ⟨P,hP,hmax⟩ := Set.exists_max_image C (natRank M) hCfin
    ⟨S,hS,Set.Subset.rfl,hSL⟩
  have hPL : P ⊂ L := Set.ssubset_iff_subset_ne.mpr ⟨hP.2.2,by
    intro heq; exact hnL (heq ▸ hP.1)⟩
  refine ⟨P,hP.1,hP.2.1,hPL,?_⟩
  have hLr := corankTwo_natRank hL
  have hlt := natRank_lt_of_flat_ssubset hP.1.1 hL.1 hPL
  by_contra hneq
  have hgap : natRank M P + 4 ≤ natRank M M.E := by omega
  have maximal : ∀ V, Indecomposable M V → P ⊆ V → V ⊆ L → natRank M V ≤ natRank M P := by
    intro V hV hPV hVL
    exact hmax V ⟨hV,hP.2.1.trans hPV,hVL⟩
  obtain ⟨X,Y,hX,hY,hXY,hLX,hLY⟩ := corankTwo_hyperplane_pair hL
  have uniqueX := unique_decomposable_below_endpoint hP.1 hL hPL.subset hX hY hXY hLX hLY maximal
  have uniqueY := unique_decomposable_below_endpoint hP.1 hL hPL.subset hY hX hXY.symm hLY hLX maximal
  obtain ⟨a,haL,haP⟩ := Set.not_subset.mp hPL.not_superset
  let Q := M.closure (insert a P)
  have hQ : M.IsFlat Q := M.isFlat_closure _
  have hPQ : P ⊆ Q := M.subset_closure_of_subset' (Set.subset_insert a P) hP.1.1.subset_ground
  have hQL : Q ⊆ L := (M.closure_mono (Set.insert_subset haL hPL.subset)).trans_eq hL.1.closure
  have hQr : natRank M Q = natRank M P + 1 :=
    natRank_closure_insert hP.1.1 (hL.1.subset_ground haL) haP
  have hnQ : ¬ Indecomposable M Q := by
    intro hi
    have := maximal Q hi hPQ hQL
    omega
  have heq := flat_eq_of_unique_decomposable_intersections hQ hnQ hQL hL hnL
    hX hY hXY hLX hLY
    (fun I hI hnI hQI hIX => uniqueX I hI hnI (hPQ.trans hQI) hIX)
    (fun I hI hnI hQI hIY => uniqueY I hI hnI (hPQ.trans hQI) hIY)
  have := congrArg (natRank M) heq
  omega
end TutteFormalization.Homotopy
