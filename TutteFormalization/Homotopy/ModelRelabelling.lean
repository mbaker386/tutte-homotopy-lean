import TutteFormalization.Homotopy.Elementary

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}
namespace FiniteModel
variable (N : FiniteModel n) (σ : Equiv.Perm (Fin n))
    (hr : ∀ F : Finset (Fin n), N.rank (F.image σ) = N.rank F)

include hr in
theorem closure_relabel (F : Finset (Fin n)) :
    N.closure (F.image σ) = (N.closure F).image σ := by
  ext j
  obtain ⟨i,rfl⟩ := σ.surjective j
  simp only [closure,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,σ.injective.eq_iff,exists_eq_right]
  rw [← Finset.image_insert,hr,hr]

include hr in
theorem flat_relabel {F : Finset (Fin n)} (hF : N.Flat F) : N.Flat (F.image σ) := by
  change N.closure (F.image σ) = F.image σ
  rw [closure_relabel N σ hr,hF]
include hr in
theorem flat_relabel_iff (F : Finset (Fin n)) : N.Flat (F.image σ) ↔ N.Flat F := by
  unfold Flat
  rw [closure_relabel N σ hr]
  exact Finset.image_inj σ.injective
end FiniteModel

namespace ModelEmbedding
/-- Permitted change of finite-model labels, with rank preservation proved by
its caller; this adds no elementary constructor or recognition assumption. -/
def relabel (φ : ModelEmbedding N M) (σ : Equiv.Perm (Fin n))
    (hr : ∀ F : Finset (Fin n), N.rank (F.image σ) = N.rank F) : ModelEmbedding N M where
  image F := φ.image (F.image σ)
  image_flat F hF := φ.image_flat _ (N.flat_relabel σ hr hF)
  order_iff F G hF hG := by
    rw [φ.order_iff _ _ (N.flat_relabel σ hr hF) (N.flat_relabel σ hr hG)]
    exact Finset.image_subset_image_iff σ.injective
  map_join F G hF hG := by
    rw [← N.closure_relabel σ hr,Finset.image_union]
    exact φ.map_join _ _ (N.flat_relabel σ hr hF) (N.flat_relabel σ hr hG)
  map_top := by
    have hu : Finset.univ.image σ = Finset.univ := Finset.image_univ_of_surjective σ.surjective
    rw [hu,φ.map_top]
  relative_rank F hF := by
    rw [φ.relative_rank _ (N.flat_relabel σ hr hF),hr,Finset.image_empty]
theorem exactCut_relabel (φ : ModelEmbedding N M) (σ : Equiv.Perm (Fin n))
    (hr : ∀ F : Finset (Fin n), N.rank (F.image σ) = N.rank F)
    {Γ : Set (Set α)} {C C' : Finset (Finset (Fin n))}
    (h : ExactCut φ Γ C') (hc : C.image (fun F => F.image σ) = C') :
    ExactCut (φ.relabel σ hr) Γ C := by
  ext F
  change (N.Flat F ∧ φ.image (F.image σ) ∈ cutPlus M Γ) ↔ F ∈ C
  have hh : (N.Flat F ∧ φ.image (F.image σ) ∈ cutPlus M Γ) ↔ F.image σ ∈ C' := by
    change _ ↔ F.image σ ∈ (C' : Set (Finset (Fin n)))
    rw [← h]
    change _ ↔ (N.Flat (F.image σ) ∧ _)
    rw [N.flat_relabel_iff σ hr]
  rw [hh,← hc,Finset.mem_image]
  constructor
  · rintro ⟨G,hG,hGF⟩
    have heq : G = F := (Finset.image_inj σ.injective).mp hGF
    exact heq ▸ hG
  · intro hF
    exact ⟨F,hF,rfl⟩
end ModelEmbedding
end TutteFormalization.Homotopy
