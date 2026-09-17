import TutteFormalization.Homotopy.ContractPaths
import TutteFormalization.Homotopy.Elementary

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {D : Set α} {n : ℕ} {N : FiniteModel n}
namespace ModelEmbedding

/-- Forward transport of the full finite model, including relative ranks and joins. -/
def liftContraction (φ : ModelEmbedding N (M ／ D)) (hD : M.IsFlat D) (h0 : N.Flat ∅) :
    ModelEmbedding N M where
  image F := φ.image F ∪ D
  image_flat F hF := flat_union_of_contract_flat hD (φ.image_flat F hF)
  order_iff F G hF hG := (union_subset_union_iff (φ.image_flat F hF).subset_ground).trans
    (φ.order_iff F G hF hG)
  map_join F G hF hG := by
    rw [φ.map_join F G hF hG,closure_union_contract hD]
    congr 1
    tauto_set
  map_top := by
    rw [φ.map_top]
    exact Set.sdiff_union_of_subset hD.subset_ground
  relative_rank F hF := by
    have hF' := natRank_contract_add D (φ.image F) hD.subset_ground (φ.image_flat F hF).subset_ground
    have h0' := natRank_contract_add D (φ.image ∅) hD.subset_ground (φ.image_flat ∅ h0).subset_ground
    have hr := φ.relative_rank F hF
    omega

theorem liftContraction_inducedCut (φ : ModelEmbedding N (M ／ D)) (hD : M.IsFlat D)
    (h0 : N.Flat ∅) (Γ : Set (Set α)) :
    (φ.liftContraction hD h0).InducedCut Γ = φ.InducedCut (contractionCut M D Γ) := by
  ext F
  change (N.Flat F ∧ φ.image F ∪ D ∈ cutPlus M Γ) ↔
    (N.Flat F ∧ φ.image F ∈ cutPlus (M ／ D) (contractionCut M D Γ))
  constructor
  · rintro ⟨hF,hmem⟩
    exact ⟨hF,(mem_cutPlus_contractionCut_iff hD (φ.image_flat F hF)).mpr hmem⟩
  · rintro ⟨hF,hmem⟩
    exact ⟨hF,(mem_cutPlus_contractionCut_iff hD (φ.image_flat F hF)).mp hmem⟩
end ModelEmbedding

theorem exactCut_liftContraction (φ : ModelEmbedding N (M ／ D)) (hD : M.IsFlat D)
    (h0 : N.Flat ∅) {Γ : Set (Set α)} {C : Finset (Finset (Fin n))}
    (h : ExactCut φ (contractionCut M D Γ) C) : ExactCut (φ.liftContraction hD h0) Γ C := by
  unfold ExactCut
  rw [ModelEmbedding.liftContraction_inducedCut]
  exact h

/-- All five exact labelled families lift. No recognition premise or extra move
is added; full cuts, ambient indecomposability and words are transported. -/
theorem BaseElementary.liftContraction {Γ : Set (Set α)} {p : TuttePath (M ／ D)}
    (h : BaseElementary (M ／ D) (contractionCut M D Γ) p) (hD : M.IsFlat D) :
    BaseElementary M Γ (p.liftContraction hD) := by
  cases h with
  | first φ p hcut hbottom hword hclosed hoff =>
    refine BaseElementary.first (φ.liftContraction hD u22_simple.1) (p.liftContraction hD)
      (exactCut_liftContraction φ hD u22_simple.1 hcut) ?_ ?_
      (p.liftContraction_closed hD hclosed) (p.liftContraction_off_normalized hD hoff)
    · exact (indecomposable_union_contract_iff hD hbottom.1).mpr hbottom
    · rw [TuttePath.liftContraction_word,hword,List.map_map]
      rfl
  | secondA φ p hcut hword hclosed hoff =>
    refine BaseElementary.secondA (φ.liftContraction hD u23_simple.1) (p.liftContraction hD)
      (exactCut_liftContraction φ hD u23_simple.1 hcut) ?_
      (p.liftContraction_closed hD hclosed) (p.liftContraction_off_normalized hD hoff)
    rw [TuttePath.liftContraction_word,hword,List.map_map]
    rfl
  | secondB φ p hcut hpoints hword hclosed hoff =>
    refine BaseElementary.secondB (φ.liftContraction hD u33_simple.1) (p.liftContraction hD)
      (exactCut_liftContraction φ hD u33_simple.1 hcut) ?_ ?_
      (p.liftContraction_closed hD hclosed) (p.liftContraction_off_normalized hD hoff)
    · intro i
      exact (indecomposable_union_contract_iff hD (hpoints i).1).mpr (hpoints i)
    · rw [TuttePath.liftContraction_word,hword,List.map_map]
      rfl
  | third φ p hcut hword hclosed hoff =>
    refine BaseElementary.third (φ.liftContraction hD u34_simple.1) (p.liftContraction hD)
      (exactCut_liftContraction φ hD u34_simple.1 hcut) ?_
      (p.liftContraction_closed hD hclosed) (p.liftContraction_off_normalized hD hoff)
    rw [TuttePath.liftContraction_word,hword,List.map_map]
    rfl
  | fourth φ p hcut h14 h25 h36 hword hclosed hoff =>
    refine BaseElementary.fourth (φ.liftContraction hD bipartite_simple.1) (p.liftContraction hD)
      (exactCut_liftContraction φ hD bipartite_simple.1 hcut) ?_ ?_ ?_ ?_
      (p.liftContraction_closed hD hclosed) (p.liftContraction_off_normalized hD hoff)
    · intro hi
      exact h14 ((indecomposable_union_contract_iff hD (φ.image_flat _ (by decide))).mp hi)
    · intro hi
      exact h25 ((indecomposable_union_contract_iff hD (φ.image_flat _ (by decide))).mp hi)
    · intro hi
      exact h36 ((indecomposable_union_contract_iff hD (φ.image_flat _ (by decide))).mp hi)
    · rw [TuttePath.liftContraction_word,hword,List.map_map]
      rfl
end TutteFormalization.Homotopy
