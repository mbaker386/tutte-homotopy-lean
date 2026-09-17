import TutteFormalization.Homotopy.PencilCorrespondence
import TutteFormalization.Homotopy.CountingPigeonhole

namespace TutteFormalization.Homotopy.CountingFrame
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
variable {s : SpecialData M Γ} (c : CountingFrame s)

/-- B.26's original two-pencil counting argument. The first pencil has exactly
three hyperplanes, and its two non-W members have opposite cut poles. -/
theorem first_pencil_count (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAW : A ⊆ s.W) (hnAY : ¬ A ⊆ s.Y) :
    ∃ H K, IsHyperplane M H ∧ IsHyperplane M K ∧
      M.closure (A ∪ s.F₁) ⊆ H ∧ M.closure (A ∪ s.F₁) ⊆ K ∧
      H ≠ s.W ∧ K ≠ s.W ∧ H ≠ K ∧ H ∈ Γ ∧ K ∉ Γ ∧
      M.closure ((H ∩ c.T) ∪ s.F₂) ∉ Γ ∧
      M.closure ((K ∩ c.T) ∪ s.F₂) ∈ Γ ∧
      ∀ J, IsHyperplane M J → M.closure (A ∪ s.F₁) ⊆ J →
        J = s.W ∨ J = H ∨ J = K := by
  let L₁ := M.closure (A ∪ s.F₁)
  let L₂ := M.closure (A ∪ s.F₂)
  have hL₁ := s.typeA_first_join ha
  have hL₂ := s.typeA_second_join ha
  have hL₁W : L₁ ⊆ s.W :=
    (M.closure_mono (Set.union_subset hAW (fun _ h => h.1.1))).trans_eq s.hW.1.closure
  have hL₂W : L₂ ⊆ s.W :=
    (M.closure_mono (Set.union_subset hAW Set.inter_subset_right)).trans_eq s.hW.1.closure
  let P := {H : Set α // IsHyperplane M H ∧ L₁ ⊆ H ∧ H ≠ s.W}
  let f (H : P) := M.closure ((H.val ∩ c.T) ∪ s.F₂)
  have hb (H : P) := c.pencil_inter_typeB ha hAW hnAY H.property.1 H.property.2.1 H.property.2.2
  have hf (H : P) : IsHyperplane M (f H) := s.typeB_second_pole (hb H).1
  have hLf (H : P) : L₂ ⊆ f H := M.closure_mono (Set.union_subset_union_left _ (hb H).2)
  have hinj : Function.Injective f := by
    intro H K heq
    have ht : H.val ∩ c.T = K.val ∩ c.T :=
      (c.second_pole_trace (hb H).1).symm.trans
        ((congrArg (fun Z => Z ∩ c.T) heq).trans (c.second_pole_trace (hb K).1))
    apply Subtype.ext
    exact (c.pencil_first_pole ha hAW hnAY H.property.1 H.property.2.1 H.property.2.2).symm.trans
      ((congrArg (fun Z => M.closure (Z ∪ s.F₁)) ht).trans
        (c.pencil_first_pole ha hAW hnAY K.property.1 K.property.2.1 K.property.2.2))
  have cover (H : P) : H.val ∈ Γ ∨ f H ∈ Γ := by
    have hp := s.pole_in_cut hM hΓ (by decide : 3 ≤ 3) hlower c.rankD hnot (hb H).1
    rw [c.pencil_first_pole ha hAW hnAY H.property.1 H.property.2.1 H.property.2.2] at hp
    exact hp
  have up (H K : P) (hH : H.val ∈ Γ) (hK : K.val ∈ Γ) : H = K :=
    Subtype.ext (cut_hyperplanes_unique_above hΓ hL₁.2 s.hW hL₁W s.offW
      H.property.1 K.property.1 H.property.2.1 K.property.2.1 hH hK)
  have uq (H K : P) (hH : f H ∈ Γ) (hK : f K ∈ Γ) : H = K :=
    hinj (cut_hyperplanes_unique_above hΓ hL₂.2 s.hW hL₂W s.offW
      (hf H) (hf K) (hLf H) (hLf K) hH hK)
  have two : ∃ H K : P, H ≠ K := by
    obtain ⟨H,K,hH,hK,hLH,hLK,hHW,hKW,hHK⟩ :=
      exists_two_other_hyperplanes (Q := s.W) hL₁.1 hL₁.2
    exact ⟨⟨H,hH,hLH,hHW⟩,⟨K,hK,hLK,hKW⟩,fun he => hHK (congrArg Subtype.val he)⟩
  obtain ⟨H,K,hHK,hHi,hKi,hHo,hKo,hall⟩ :=
    two_slots_exactly_two (fun H : P => H.val ∈ Γ) (fun H => f H ∈ Γ) cover up uq two
  refine ⟨H.val,K.val,H.property.1,K.property.1,H.property.2.1,K.property.2.1,
    H.property.2.2,K.property.2.2,fun he => hHK (Subtype.ext he),hHi,hKo,hHo,hKi,?_⟩
  intro J hJ hLJ
  by_cases hJW : J = s.W
  · exact Or.inl hJW
  rcases hall ⟨J,hJ,hLJ,hJW⟩ with he | he
  · exact Or.inr (Or.inl (congrArg Subtype.val he))
  · exact Or.inr (Or.inr (congrArg Subtype.val he))
end TutteFormalization.Homotopy.CountingFrame
