import TutteFormalization.Homotopy.Embedding
import TutteFormalization.ContractionFlats

namespace TutteFormalization.Homotopy
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {D F G : Set α}

theorem union_sdiff_eq_self (hF : F ⊆ M.E \ D) : (F ∪ D) \ D = F := by
  ext e
  constructor
  · rintro ⟨he | he,hn⟩
    · exact he
    · exact False.elim (hn he)
  · intro he; exact ⟨Or.inl he,(hF he).2⟩

theorem union_subset_union_iff (hF : F ⊆ M.E \ D) : F ∪ D ⊆ G ∪ D ↔ F ⊆ G := by
  constructor
  · intro h e he
    exact (h (Or.inl he)).resolve_right (hF he).2
  · intro h; exact Set.union_subset_union_left D h

theorem union_eq_union_iff (hF : F ⊆ M.E \ D) (hG : G ⊆ M.E \ D) :
    F ∪ D = G ∪ D ↔ F = G := by
  constructor
  · intro h
    exact ((union_subset_union_iff hF).mp h.subset).antisymm
      ((union_subset_union_iff hG).mp h.symm.subset)
  · rintro rfl; rfl

theorem indecomposable_union_contract_iff (hD : M.IsFlat D) (hF : (M ／ D).IsFlat F) :
    Indecomposable M (F ∪ D) ↔ Indecomposable (M ／ D) F := by
  have h := indecomposable_sdiff_contract_iff (flat_union_of_contract_flat hD hF)
    (Set.subset_union_right : D ⊆ F ∪ D)
  simpa only [union_sdiff_eq_self hF.subset_ground] using h.symm

theorem corankTwo_union_contract (hD : M.IsFlat D) (hF : CorankTwo (M ／ D) F) :
    CorankTwo M (F ∪ D) := by
  refine ⟨flat_union_of_contract_flat hD hF.1, ?_⟩
  have hrF := natRank_contract_add D F hD.subset_ground hF.1.subset_ground
  have hrE := natRank_contract_add D (M.E \ D) hD.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset hD.subset_ground] at hrE
  have hr : natRank (M ／ D) F + 2 = natRank (M ／ D) (M ／ D).E := by
    have hr := hF.2
    rw [← cast_natRank (M ／ D) F, ← cast_natRank (M ／ D) (M ／ D).E] at hr
    exact_mod_cast hr
  change natRank (M ／ D) (M ／ D).E + natRank M D = _ at hrE
  rw [← cast_natRank M (F ∪ D), ← cast_natRank M M.E]
  exact_mod_cast (show natRank M (F ∪ D) + 2 = natRank M M.E by omega)

theorem closure_union_contract (hD : M.IsFlat D) (S : Set α) :
    (M ／ D).closure S ∪ D = M.closure (S ∪ D) := by
  rw [M.contract_closure_eq]
  exact Set.sdiff_union_of_subset
    (M.subset_closure_of_subset' Set.subset_union_right hD.subset_ground)

theorem modularPair_union_contract (hD : M.IsFlat D) (hFG : ModularPair (M ／ D) F G) :
    ModularPair M (F ∪ D) (G ∪ D) := by
  have hI : (F ∪ D) ∩ (G ∪ D) = (F ∩ G) ∪ D := by tauto_set
  have hU : (F ∪ D) ∪ (G ∪ D) = (F ∪ G) ∪ D := by tauto_set
  refine ⟨flat_union_of_contract_flat hD hFG.1,flat_union_of_contract_flat hD hFG.2.1,?_⟩
  have hr : natRank (M ／ D) F + natRank (M ／ D) G =
      natRank (M ／ D) (F ∩ G) + natRank (M ／ D) ((M ／ D).closure (F ∪ G)) := by
    have hr := hFG.2.2
    rw [← cast_natRank (M ／ D) F, ← cast_natRank (M ／ D) G,
      ← cast_natRank (M ／ D) (F ∩ G),
      ← cast_natRank (M ／ D) ((M ／ D).closure (F ∪ G))] at hr
    exact_mod_cast hr
  have hFr := natRank_contract_add D F hD.subset_ground hFG.1.subset_ground
  have hGr := natRank_contract_add D G hD.subset_ground hFG.2.1.subset_ground
  have hIr := natRank_contract_add D (F ∩ G) hD.subset_ground
    (Set.inter_subset_left.trans hFG.1.subset_ground)
  have hJr := natRank_contract_add D ((M ／ D).closure (F ∪ G)) hD.subset_ground
    ((M ／ D).closure_subset_ground _)
  rw [closure_union_contract hD] at hJr
  rw [hI,hU,← cast_natRank M (F ∪ D),← cast_natRank M (G ∪ D),
    ← cast_natRank M ((F ∩ G) ∪ D),← cast_natRank M (M.closure ((F ∪ G) ∪ D))]
  exact_mod_cast (show natRank M (F ∪ D) + natRank M (G ∪ D) =
    natRank M ((F ∩ G) ∪ D) + natRank M (M.closure ((F ∪ G) ∪ D)) by omega)

/-- The full induced cut on the contracted flat interval, with no nonempty premise. -/
def contractionCut (M : Matroid α) (D : Set α) (Γ : Set (Set α)) : Set (Set α) :=
  {F | (M ／ D).IsFlat F ∧ F ∪ D ∈ Γ}

theorem contractionCut_modular (hD : M.IsFlat D) {Γ : Set (Set α)} (hΓ : ModularCut M Γ) :
    ModularCut (M ／ D) (contractionCut M D Γ) where
  isFlat _ h := h.1
  upward F G hF hG hFG := ⟨hG,hΓ.upward _ _ hF.2 (flat_union_of_contract_flat hD hG)
    (Set.union_subset_union_left D hFG)⟩
  inter_mem F G hF hG hFG := by
    refine ⟨flat_inter hF.1 hG.1,?_⟩
    have h := hΓ.inter_mem _ _ hF.2 hG.2 (modularPair_union_contract hD hFG)
    have heq : (F ∪ D) ∩ (G ∪ D) = (F ∩ G) ∪ D := by tauto_set
    simpa only [heq] using h

theorem mem_cutPlus_contractionCut_iff (hD : M.IsFlat D) {Γ : Set (Set α)}
    (hF : (M ／ D).IsFlat F) :
    F ∈ cutPlus (M ／ D) (contractionCut M D Γ) ↔ F ∪ D ∈ cutPlus M Γ := by
  have htop : F = (M ／ D).E ↔ F ∪ D = M.E := by
    constructor
    · rintro rfl
      exact Set.sdiff_union_of_subset hD.subset_ground
    · intro h
      have := congrArg (fun S => S \ D) h
      change F = M.E \ D
      simpa only [union_sdiff_eq_self hF.subset_ground] using this
  simp only [cutPlus,Set.mem_union,Set.mem_singleton_iff,contractionCut,Set.mem_setOf_eq,
    hF,true_and,htop]
end TutteFormalization.Homotopy
