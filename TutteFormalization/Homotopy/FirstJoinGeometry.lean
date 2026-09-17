import TutteFormalization.Homotopy.CoverJoin
import TutteFormalization.Homotopy.CutHyperplaneCriterion

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.2: L=G∨F has corank two, lies in the preceding hyperplane,
and is outside the cut. The source's rank calculation uses G∩F=D. -/
theorem corankThree_first_join (hΓ : ModularCut M Γ) {D G F H K : Set α}
    (hD : M.IsFlat D) (hG : M.IsFlat G) (hF : M.IsFlat F)
    (hDG : D ⊆ G) (hDF : D ⊆ F) (hrG : natRank M G = natRank M D + 1)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hH : IsHyperplane M H) (hGH : G ⊆ H) (hFH : F ⊆ H)
    (hFK : F ⊆ K) (hGK : ¬ G ⊆ K) (hoff : H ∉ Γ) :
    CorankTwo M (M.closure (G ∪ F)) ∧ M.closure (G ∪ F) ⊆ H ∧
      M.closure (G ∪ F) ∉ Γ := by
  have hn : ¬ G ⊆ F := fun h => hGK (h.trans hFK)
  have hr := (cover_join_rank hD hG hF hDG hDF hrG hn).2
  have hc : CorankTwo M (M.closure (G ∪ F)) := by
    rw [corankTwo_iff_natRank (M.isFlat_closure _)]
    omega
  have hLH : M.closure (G ∪ F) ⊆ H :=
    (M.closure_mono (Set.union_subset hGH hFH)).trans_eq hH.1.closure
  refine ⟨hc,hLH,?_⟩
  intro hm
  exact hoff (hΓ.upward _ _ hm hH.1 hLH)

/-- Joining two distinct corank-two covers of a corank-three flat gives
an actual hyperplane, with both rank bounds explicit. -/
theorem corankThree_join_covers {F L Q : Set α} (hF : M.IsFlat F)
    (hrF : natRank M F + 3 = natRank M M.E)
    (hL : CorankTwo M L) (hQ : CorankTwo M Q)
    (hFL : F ⊆ L) (hFQ : F ⊆ Q) (hne : L ≠ Q) :
    IsHyperplane M (M.closure (L ∪ Q)) ∧ L ∩ Q = F := by
  have hrL := corankTwo_natRank hL
  have hrQ := corankTwo_natRank hQ
  have hi := cover_flats_inter_eq hF hL.1 hQ.1 hFL hFQ (by omega) (by omega) hne
  have hr := rank_join_of_distinct_covers hL.1 hQ.1 (by omega) (by omega) hne hi
  exact ⟨isHyperplane_of_natRank (M.isFlat_closure _) (by omega),hi⟩
end TutteFormalization.Homotopy
