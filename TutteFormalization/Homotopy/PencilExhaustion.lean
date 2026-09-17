import TutteFormalization.Homotopy.PencilCounting

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)
include c

/-- The indecomposable corank-two flats below T and above D are precisely
its type-(b) transversals; its two intersections with W,Y are decomposable. -/
theorem typeB_of_below_T {B : Set α} (hB : Indecomposable M B)
    (hcB : CorankTwo M B) (hDB : s.D ⊆ B) (hBT : B ⊆ c.T) : s.TypeB B := by
  have hrB := corankTwo_natRank hcB
  have hrD := c.rankD
  refine ⟨hB,hDB,by omega,?_,?_⟩
  · intro hBW
    have hr := corankTwo_natRank c.corankWT
    have he := flat_eq_of_subset_of_natRank_le hB.1 c.corankWT.1
      (Set.subset_inter hBW hBT) (by omega)
    exact c.decompWT (he ▸ hB)
  · intro hBY
    have hr := corankTwo_natRank c.corankYT
    have he := flat_eq_of_subset_of_natRank_le hB.1 c.corankYT.1
      (Set.subset_inter hBY hBT) (by omega)
    exact c.decompYT (he ▸ hB)

/-- B.26's second injection: all intermediate indecomposable flats are the
two traces supplied by the first pencil. -/
theorem intermediate_exhaustion {A H K : Set α} (ha : s.TypeA A)
    (hall : ∀ J, IsHyperplane M J → M.closure (A ∪ s.F₁) ⊆ J →
      J = s.W ∨ J = H ∨ J = K)
    {B : Set α} (hB : Indecomposable M B) (hcB : CorankTwo M B)
    (hAB : A ⊆ B) (hBT : B ⊆ c.T) : B = H ∩ c.T ∨ B = K ∩ c.T := by
  have hb := c.typeB_of_below_T hB hcB (ha.2.1.trans hAB) hBT
  let J := M.closure (B ∪ s.F₁)
  have hBJ : B ⊆ J := M.subset_closure_of_subset' Set.subset_union_left hB.1.subset_ground
  rcases hall J (s.typeB_first_pole hb) (M.closure_mono (Set.union_subset_union_left _ hAB)) with he | he | he
  · exact False.elim (hb.2.2.2.1 (hBJ.trans_eq he))
  · exact Or.inl ((c.first_pole_trace hb).symm.trans (congrArg (fun Z => Z ∩ c.T) he))
  · exact Or.inr ((c.first_pole_trace hb).symm.trans (congrArg (fun Z => Z ∩ c.T) he))

/-- B.26: exactly two cut hyperplanes contain a type-(a) transversal on W.
The proof retains the pencil count, trace exhaustion, and modular-cut contradiction. -/
theorem cut_above_typeA_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ A ⊆ U ∧ A ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → A ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  obtain ⟨H,K,hH,hK,hLH,hLK,hHW,hKW,hHK,hHi,hKo,hHo,hKi,hall⟩ :=
    c.first_pencil_count hM hΓ hlower hnot ha hAW hnAY
  have hbH := c.pencil_inter_typeB ha hAW hnAY hH hLH hHW
  have hbK := c.pencil_inter_typeB ha hAW hnAY hK hLK hKW
  let V := M.closure ((K ∩ c.T) ∪ s.F₂)
  have hV : IsHyperplane M V := s.typeB_second_pole hbK.1
  have hKV : K ∩ c.T ⊆ V :=
    M.subset_closure_of_subset' Set.subset_union_left hbK.1.1.1.subset_ground
  have hcH : CorankTwo M (H ∩ c.T) := (corankTwo_iff_natRank hbH.1.1.1).mpr (by
    have := hbH.1.2.2.1; have := c.rankD; omega)
  have hcK : CorankTwo M (K ∩ c.T) := (corankTwo_iff_natRank hbK.1.1.1).mpr (by
    have := hbK.1.2.2.1; have := c.rankD; omega)
  have hHV : H ≠ V := by
    intro he
    have ht : H ∩ c.T = K ∩ c.T :=
      (congrArg (fun Z => Z ∩ c.T) he).trans (c.second_pole_trace hbK.1)
    exact hHK ((c.pencil_first_pole ha hAW hnAY hH hLH hHW).symm.trans
      ((congrArg (fun Z => M.closure (Z ∪ s.F₁)) ht).trans
        (c.pencil_first_pole ha hAW hnAY hK hLK hKW)))
  refine ⟨H,V,hH,hV,hbH.2.trans Set.inter_subset_left,hbK.2.trans hKV,hHi,hKi,hHV,?_⟩
  intro J hJ hAJ hJi
  have hrA : natRank M A + 3 = natRank M M.E := by
    have := ha.2.2.1; have := c.rankD; omega
  have hWT : s.W ≠ c.T := by
    intro he
    have hr := corankTwo_natRank c.corankWT
    rw [he,Set.inter_self] at hr
    have := hyperplane_natRank c.hT; omega
  have hed := third_hyperplane_adjacent ha.1 hrA c.corankWT c.decompWT
    (Set.subset_inter hAW (c.typeA_below_T ha)) s.hW c.hT hWT
    Set.inter_subset_left Set.inter_subset_right hJ
    (fun he => s.offW (he ▸ hJi)) (fun he => c.offT (he ▸ hJi)) hAJ
  rcases c.intermediate_exhaustion ha hall hed.2.2.1 hed.2.2.2
    (Set.subset_inter hAJ (c.typeA_below_T ha)) Set.inter_subset_right with he | he
  · exact Or.inl (cut_hyperplanes_unique_above hΓ hcH c.hT Set.inter_subset_right c.offT
      hJ hH (he ▸ Set.inter_subset_left) Set.inter_subset_left hJi hHi)
  · exact Or.inr (cut_hyperplanes_unique_above hΓ hcK c.hT Set.inter_subset_right c.offT
      hJ hV (he ▸ Set.inter_subset_left) hKV hJi hKi)
end TutteFormalization.Homotopy.CountingFrame
