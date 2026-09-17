import TutteFormalization.Homotopy.FirstIntersection
import TutteFormalization.Homotopy.SpecialSymmetry
import TutteFormalization.Homotopy.TransversalContainment
import TutteFormalization.Homotopy.TransversalChoice

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.21, retaining the new-transversal construction above B∩Y. A bare exchange
of names would not ensure the new join lies below the original I. -/
theorem second_intersection_decomposable (s : SpecialData M Γ)
    (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ} (hn : 3 ≤ n)
    (hlower : Lower M Γ n) (hrD : natRank M s.D + (n+1) = natRank M M.E)
    (hnot : ¬ NullHomotopic M Γ s.path) {A B C I : Set α}
    (ha : s.TypeA A) (hb : s.TypeB B) (hc : s.TypeB C)
    (hAW : A ⊆ s.W) (hAB : A ⊆ B) (hAC : A ⊆ C)
    (hoB : M.closure (B ∪ s.F₁) ∉ Γ) (hoC : M.closure (C ∪ s.F₂) ∉ Γ)
    (hI : IsHyperplane M I) (hBI : B ⊆ I) (hCI : C ⊆ I) (hIo : I ∉ Γ) :
    ¬ Indecomposable M (s.W ∩ I) ∧ CorankTwo M (s.W ∩ I) := by
  have hYI := s.first_intersection_decomposable hM hΓ hn hlower hrD hnot
    ha hb hc hAW hAB hAC hoB hoC hI hBI hCI hIo
  have hib := s.typeB_intersections hb
  let A' := B ∩ s.Y
  have hA'r : natRank M A' = natRank M s.D + 1 := hib.2.2.2.1
  have hnA'W : ¬ A' ⊆ s.W := by
    intro h
    have hsub : A' ⊆ s.D := (Set.subset_inter (Set.subset_inter Set.inter_subset_left h)
      Set.Subset.rfl).trans_eq hib.2.2.2.2.1
    have hh := natRank_mono (M := M) hsub
    omega
  have ha' : s.TypeA A' := ⟨hib.2.1,Set.subset_inter hb.2.1 s.D_subset_Y,hA'r,
    fun h => hnA'W (h.trans Set.inter_subset_left)⟩
  have ha's : s.swap.TypeA A' := (s.swap_typeA A').mpr ha'
  have hL := s.swap.typeA_second_join ha's
  have hLY : M.closure (A' ∪ s.swap.F₂) ⊆ s.Y := by
    apply (M.closure_mono (Set.union_subset Set.inter_subset_right ?_)).trans_eq s.hY.1.closure
    rw [s.swap_second]
    exact fun _ hf => hf.1.1
  obtain ⟨Z'',hZ'',hLZ,hZY,hZo⟩ := exists_other_off_hyperplane hΓ hL.1 hL.2 s.hY hLY s.offY
  have hA'Z : A' ⊆ Z'' := (M.subset_closure_of_subset' Set.subset_union_left hib.2.1.1.subset_ground).trans hLZ
  have hF₂Z : s.swap.F₂ ⊆ Z'' := (M.subset_closure_of_subset' Set.subset_union_right
    s.swap.second_indec.1.subset_ground).trans hLZ
  obtain ⟨B'',hb''s,hA'B'',hB''Z⟩ := s.swap.exists_typeB_under ha's Set.inter_subset_right
    hnA'W hZ'' hA'Z hZY
  have hb'' : s.TypeB B'' := (s.swap_typeB B'').mp hb''s
  have hsecond := pole_eq_of_containment hB''Z hF₂Z hZ'' (s.swap.typeB_second_pole hb''s)
  have hsecondOff : M.closure (B'' ∪ s.swap.F₂) ∉ Γ := hsecond ▸ hZo
  have hYIne : s.Y ≠ I := fun h => hb.2.2.2.2 (hBI.trans_eq h.symm)
  have hB''I : B'' ⊆ I := extension_below_other_hyperplane s.hY hI hYIne hYI.2 hYI.1
    hb''.1.1 hA'B'' (Set.subset_inter Set.inter_subset_right (Set.inter_subset_left.trans hBI))
    (by have := hb''.2.2.1; omega) hb''.2.2.2.2
  have hnotSwap : ¬ NullHomotopic M Γ s.swap.path := fun h => hnot ((s.swap_null_iff hΓ).mp h)
  have hrSwap : natRank M s.swap.D + (n+1) = natRank M M.E := by simpa using hrD
  have hoBs : M.closure (B ∪ s.swap.F₁) ∉ Γ := by simpa using hoB
  exact s.swap.first_intersection_decomposable hM hΓ hn hlower hrSwap hnotSwap
    ha's ((s.swap_typeB B).mpr hb) hb''s Set.inter_subset_right Set.inter_subset_left hA'B''
    hoBs hsecondOff hI hBI hB''I hIo
end TutteFormalization.Homotopy.SpecialData
