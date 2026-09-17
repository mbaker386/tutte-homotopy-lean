import TutteFormalization.Homotopy.SixModelPlanes
import TutteFormalization.Homotopy.CubeDegreeCount

namespace TutteFormalization.Homotopy.SixFlatData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

theorem cube_flat (i : Fin 8) : bipartiteModel.Flat (cubeTriple i) :=
  (bipartite_flats _).mpr (Or.inr (Or.inl (cubeTriple_geometry i).2.1))

theorem cube_hyperplane (i : Fin 8) : IsHyperplane M (d.ambientModel.image (cubeTriple i)) :=
  d.model_hyperplane (cubeTriple_geometry i).2.1

theorem cube_images_injective : Function.Injective (fun i => d.ambientModel.image (cubeTriple i)) := by
  intro i j he
  exact cubeTriple_injective (d.ambientModel.injective_flats (cube_flat i) (cube_flat j) he)

theorem point_below_cube_iff (k : Fin 6) (i : Fin 8) :
    d.point k ⊆ d.ambientModel.image (cubeTriple i) ↔ k ∈ cubeTriple i := by
  rw [← d.ambientModel_singleton k]
  have hk : bipartiteModel.Flat {k} := by
    apply (bipartite_flats _).mpr; left; simp
  rw [d.ambientModel.order_iff _ _ hk (cube_flat i),Finset.singleton_subset_iff]

/-- Every cut hyperplane above D is one of the actual cube triples, since
all three represented pair-planes are off the normalized cut. -/
theorem cut_hyperplane_cube {H : Set α} (hH : IsHyperplane M H) (hDH : s.D ⊆ H)
    (hiH : H ∈ cutPlus M Γ) : ∃ i, d.ambientModel.image (cubeTriple i) = H := by
  obtain ⟨F,hF,he⟩ := d.hyperplanes_recognized hH hDH
  have cases : ∀ F ∈ bipartiteHyperplanes, F ∈ fourCircuits ∨ ∃ i, cubeTriple i = F := by decide
  rcases cases F hF with hc | ⟨i,hi⟩
  · exact False.elim (d.circuit_off hc (he.symm ▸ hiH))
  · exact ⟨i,hi.symm ▸ he⟩

include d in
/-- B.26/B.27 provide the actual two cut hyperplanes above each of the six
labels, before any finite-model cut classification is used. -/
theorem point_two_cut (hM : Connected M) (hΓ : ModularCut M Γ) (hlower : Lower M Γ 3)
    (hnot : ¬ NullHomotopic M Γ s.path) (i : Fin 6) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ d.point i ⊆ U ∧ d.point i ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → d.point i ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  have hr : natRank M (d.point i) + 3 = natRank M M.E := by
    have := d.rank i; have := c.rankD; omega
  rcases c.corankThree_classification hM hΓ hlower hnot (d.indec i) (d.above i) hr with he | he | ha
  · rw [he]; exact c.first_two_cut_hyperplanes hM hΓ hlower hnot
  · rw [he]; exact c.second_two_cut_hyperplanes hM hΓ hlower hnot
  · exact c.cut_above_typeA hM hΓ hlower hnot ha

noncomputable def cutTriples : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter (fun i => d.ambientModel.image (cubeTriple i) ∈ cutPlus M Γ)

theorem mem_cutTriples (i : Fin 8) : i ∈ d.cutTriples ↔
    d.ambientModel.image (cubeTriple i) ∈ cutPlus M Γ := by
  classical
  simp only [cutTriples,Finset.mem_filter,Finset.mem_univ,true_and]

theorem cutTriples_degree_two (hM : Connected M) (hΓ : ModularCut M Γ) (hlower : Lower M Γ 3)
    (hnot : ¬ NullHomotopic M Γ s.path) (k : Fin 6) :
    (d.cutTriples.filter (fun i => k ∈ cubeTriple i)).card = 2 := by
  classical
  obtain ⟨U,V,hU,hV,hkU,hkV,hiU,hiV,hUV,all⟩ := d.point_two_cut hM hΓ hlower hnot k
  obtain ⟨x,hx⟩ := d.cut_hyperplane_cube hU ((d.above k).trans hkU) (Or.inl hiU)
  obtain ⟨y,hy⟩ := d.cut_hyperplane_cube hV ((d.above k).trans hkV) (Or.inl hiV)
  have hxy : x ≠ y := fun he => hUV (hx.symm.trans ((congrArg (fun i => d.ambientModel.image (cubeTriple i)) he).trans hy))
  have hset : d.cutTriples.filter (fun i => k ∈ cubeTriple i) = {x,y} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,hkz⟩
      have hzG : d.ambientModel.image (cubeTriple z) ∈ Γ := by
        have hh := (d.mem_cutTriples z).mp hz
        rcases hh with hh | hh
        · exact hh
        · exact False.elim ((d.cube_hyperplane z).2.1 hh)
      rcases all _ (d.cube_hyperplane z) ((d.point_below_cube_iff k z).mpr hkz) hzG with he | he
      · exact Or.inl (d.cube_images_injective (he.trans hx.symm))
      · exact Or.inr (d.cube_images_injective (he.trans hy.symm))
    · intro hz
      rcases hz with hz | hz
      · subst z
        exact ⟨(d.mem_cutTriples x).mpr (hx.symm ▸ Or.inl hiU),
          (d.point_below_cube_iff k x).mp (hx.symm ▸ hkU)⟩
      · subst z
        exact ⟨(d.mem_cutTriples y).mpr (hy.symm ▸ Or.inl hiV),
          (d.point_below_cube_iff k y).mp (hy.symm ▸ hkV)⟩
  rw [hset]
  simp [hxy]

theorem cutTriples_card_four (hM : Connected M) (hΓ : ModularCut M Γ) (hlower : Lower M Γ 3)
    (hnot : ¬ NullHomotopic M Γ s.path) : d.cutTriples.card = 4 :=
  cube_degree_count d.cutTriples (d.cutTriples_degree_two hM hΓ hlower hnot)
end TutteFormalization.Homotopy.SixFlatData
