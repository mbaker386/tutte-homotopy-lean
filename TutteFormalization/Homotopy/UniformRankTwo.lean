import TutteFormalization.Homotopy.RankTableEmbedding
import TutteFormalization.Homotopy.PointRepresentatives

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Three rank-one labels with every pair spanning a rank-two ambient matroid
have precisely the approved U(2,3) rank table. -/
theorem rankTwo_label_table (e : Fin 3 → α) (he : ∀ i, e i ∈ M.E)
    (hrM : natRank M M.E = 2) (hs : ∀ i, natRank M {e i} = 1)
    (hp : ∀ i j, i ≠ j → M.closure {e i,e j} = M.E) (S : Finset (Fin 3)) :
    natRank M (e '' (S : Set (Fin 3))) = u23.rank S := by
  classical
  change _ = min S.card 2
  by_cases h0 : S = ∅
  · subst S
    simp only [Finset.coe_empty,Set.image_empty,natRank_empty,Finset.card_empty,Nat.zero_min]
  by_cases h1 : S.card = 1
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.coe_singleton,Set.image_singleton,hs,Finset.card_singleton]
    decide
  have hcard : 2 ≤ S.card := by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0); omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hpS : ({e i,e j} : Set α) ⊆ e '' (S : Set (Fin 3)) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨i,hi,rfl⟩
    · exact ⟨j,hj,rfl⟩
  have hrPair : natRank M {e i,e j} = 2 := by
    rw [← natRank_closure M _,hp i j hij,hrM]
  have hlo := natRank_mono (M := M) hpS
  have hhi := natRank_mono (M := M) (show e '' (S : Set (Fin 3)) ⊆ M.E from by
    rintro _ ⟨i,_,rfl⟩; exact he i)
  rw [Nat.min_eq_right hcard]
  omega

noncomputable def rankTwoModel (e : Fin 3 → α) (he : ∀ i, e i ∈ M.E)
    (hrM : natRank M M.E = 2) (hs : ∀ i, natRank M {e i} = 1)
    (hp : ∀ i j, i ≠ j → M.closure {e i,e j} = M.E) : ModelEmbedding u23 M :=
  ModelEmbedding.ofRankTable e he (rankTwo_label_table e he hrM hs hp) (by
    apply flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) M.ground_isFlat (M.closure_subset_ground _)
    rw [natRank_closure,rankTwo_label_table e he hrM hs hp,hrM]
    decide)
end TutteFormalization.Homotopy
