import TutteFormalization.Homotopy.ModelGeometry
import TutteFormalization.Homotopy.Cut

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {n : ℕ} {N : FiniteModel n}

/-- S3 finite-model interface. Only ambient joins are preserved. The full model
flat lattice is used; ambient intersections are deliberately not a field. -/
structure ModelEmbedding (N : FiniteModel n) (M : Matroid α) [M.Finite] where
  image : Finset (Fin n) → Set α
  image_flat : ∀ F, N.Flat F → M.IsFlat (image F)
  order_iff : ∀ F G, N.Flat F → N.Flat G → (image F ⊆ image G ↔ F ⊆ G)
  map_join : ∀ F G, N.Flat F → N.Flat G →
    image (N.closure (F ∪ G)) = M.closure (image F ∪ image G)
  map_top : image Finset.univ = M.E
  relative_rank : ∀ F, N.Flat F → natRank M (image F) = natRank M (image ∅) + N.rank F

namespace ModelEmbedding
variable (φ : ModelEmbedding N M)

def InducedCut (Γ : Set (Set α)) : Set (Finset (Fin n)) :=
  {F | N.Flat F ∧ φ.image F ∈ cutPlus M Γ}

theorem injective_flats {F G} (hF : N.Flat F) (hG : N.Flat G)
    (heq : φ.image F = φ.image G) : F = G := by
  apply Finset.Subset.antisymm
  · exact (φ.order_iff F G hF hG).mp heq.subset
  · exact (φ.order_iff G F hG hF).mp heq.symm.subset

/-- Intrinsic meet is the greatest represented lower bound, not an ambient meet assertion. -/
theorem intrinsic_meet {F G K} (hF : N.Flat F) (hG : N.Flat G) (hK : N.Flat K) :
    φ.image K ⊆ φ.image (F ∩ G) ↔ φ.image K ⊆ φ.image F ∧ φ.image K ⊆ φ.image G := by
  rw [φ.order_iff K (F ∩ G) hK (N.inter_flat hF hG),
    φ.order_iff K F hK hF, φ.order_iff K G hK hG]
  exact Finset.subset_inter_iff

theorem image_inter_subset {F G} (hF : N.Flat F) (hG : N.Flat G) :
    φ.image (F ∩ G) ⊆ φ.image F ∩ φ.image G :=
  Set.subset_inter ((φ.order_iff _ _ (N.inter_flat hF hG) hF).mpr Finset.inter_subset_left)
    ((φ.order_iff _ _ (N.inter_flat hF hG) hG).mpr Finset.inter_subset_right)

/-- The S3 submodularity argument: only modular pairs force ambient meet preservation. -/
theorem modular_inter {F G} (hF : N.Flat F) (hG : N.Flat G)
    (hr : N.rank F + N.rank G = N.rank (F ∩ G) + N.rank (N.closure (F ∪ G))) :
    φ.image (F ∩ G) = φ.image F ∩ φ.image G := by
  have hsub := natRank_submodular M (φ.image F) (φ.image G)
  rw [← φ.map_join F G hF hG] at hsub
  have hFr := φ.relative_rank F hF
  have hGr := φ.relative_rank G hG
  have hIr := φ.relative_rank (F ∩ G) (N.inter_flat hF hG)
  have hJr := φ.relative_rank (N.closure (F ∪ G)) (N.closure_flat _)
  exact flat_eq_of_subset_of_natRank_le (φ.image_flat _ (N.inter_flat hF hG))
    (flat_inter (φ.image_flat F hF) (φ.image_flat G hG)) (φ.image_inter_subset hF hG) (by omega)

theorem modularPair {F G} (hF : N.Flat F) (hG : N.Flat G)
    (hr : N.rank F + N.rank G = N.rank (F ∩ G) + N.rank (N.closure (F ∪ G))) :
    ModularPair M (φ.image F) (φ.image G) := by
  refine ⟨φ.image_flat F hF, φ.image_flat G hG, ?_⟩
  rw [← φ.modular_inter hF hG hr, ← φ.map_join F G hF hG]
  have hFr := φ.relative_rank F hF
  have hGr := φ.relative_rank G hG
  have hIr := φ.relative_rank (F ∩ G) (N.inter_flat hF hG)
  have hJr := φ.relative_rank (N.closure (F ∪ G)) (N.closure_flat _)
  rw [← cast_natRank M (φ.image F), ← cast_natRank M (φ.image G),
    ← cast_natRank M (φ.image (F ∩ G)), ← cast_natRank M (φ.image (N.closure (F ∪ G)))]
  exact_mod_cast (show natRank M (φ.image F) + natRank M (φ.image G) =
    natRank M (φ.image (F ∩ G)) + natRank M (φ.image (N.closure (F ∪ G))) by omega)

theorem induced_inter {Γ : Set (Set α)} (hΓ : ModularCut M Γ) {F G}
    (hF : F ∈ φ.InducedCut Γ) (hG : G ∈ φ.InducedCut Γ)
    (hr : N.rank F + N.rank G = N.rank (F ∩ G) + N.rank (N.closure (F ∪ G))) :
    F ∩ G ∈ φ.InducedCut Γ := by
  refine ⟨N.inter_flat hF.1 hG.1, ?_⟩
  rw [φ.modular_inter hF.1 hG.1 hr]
  exact (cutPlus_modular hΓ).inter_mem _ _ hF.2 hG.2 (φ.modularPair hF.1 hG.1 hr)

theorem induced_upward {Γ : Set (Set α)} (hΓ : ModularCut M Γ) {F G}
    (hF : F ∈ φ.InducedCut Γ) (hG : N.Flat G) (hFG : F ⊆ G) : G ∈ φ.InducedCut Γ :=
  ⟨hG, (cutPlus_modular hΓ).upward _ _ hF.2 (φ.image_flat G hG)
    ((φ.order_iff F G hF.1 hG).mpr hFG)⟩

theorem top_rank : natRank M M.E = natRank M (φ.image ∅) + N.rank Finset.univ := by
  simpa only [φ.map_top] using φ.relative_rank Finset.univ N.top_flat
/-- The selected lattice is the finite image of all model flats. -/
def Selected : Set (Set α) := φ.image '' {F | N.Flat F}

theorem selected_finite : φ.Selected.Finite := (Set.toFinite _).image φ.image

theorem selected_top : M.E ∈ φ.Selected := ⟨Finset.univ, N.top_flat, φ.map_top⟩

theorem selected_join {A B : Set α} (hA : A ∈ φ.Selected) (hB : B ∈ φ.Selected) :
    M.closure (A ∪ B) ∈ φ.Selected := by
  obtain ⟨F, hF, rfl⟩ := hA
  obtain ⟨G, hG, rfl⟩ := hB
  exact ⟨N.closure (F ∪ G), N.closure_flat _, φ.map_join F G hF hG⟩

theorem bottom_corank : natRank M M.E - natRank M (φ.image ∅) = N.rank Finset.univ := by
  rw [φ.top_rank]
  omega

theorem atom_rank {i : Fin n} (hflat : N.Flat {i}) (hrank : N.rank {i} = 1) :
    natRank M (φ.image {i}) = natRank M (φ.image ∅) + 1 := by
  simpa only [hrank] using φ.relative_rank {i} hflat
end ModelEmbedding
end TutteFormalization.Homotopy
