import TutteFormalization.Homotopy.PencilExhaustion
import TutteFormalization.Homotopy.CountingSymmetry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Proof-only record of the exact three-element pencil and its unique cut
member. Every field is proved from B.26, never assumed by the main theorem. -/
def ThreePencil (M : Matroid α) (Γ : Set (Set α)) (L Q : Set α) : Prop :=
  ∃ H K, IsHyperplane M H ∧ IsHyperplane M K ∧ L ⊆ H ∧ L ⊆ K ∧
    H ≠ Q ∧ K ≠ Q ∧ H ≠ K ∧ H ∈ Γ ∧ K ∉ Γ ∧
    ∀ J, IsHyperplane M J → L ⊆ J → J = Q ∨ J = H ∨ J = K

namespace CountingFrame
variable {s : SpecialData M Γ} (c : CountingFrame s)
include c

theorem first_three_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAW : A ⊆ s.W) :
    ThreePencil M Γ (M.closure (A ∪ s.F₁)) s.W := by
  obtain ⟨H,K,hH,hK,hLH,hLK,hHW,hKW,hHK,hHi,hKo,_,_,hall⟩ :=
    c.first_pencil_count hM hΓ hlower hnot ha hAW
      (fun hy => ha.2.2.2 (Set.subset_inter hAW hy))
  exact ⟨H,K,hH,hK,hLH,hLK,hHW,hKW,hHK,hHi,hKo,hall⟩

theorem first_three_on_Y (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAY : A ⊆ s.Y) :
    ThreePencil M Γ (M.closure (A ∪ s.F₁)) s.Y := by
  have hh := c.swap.first_three_on_W hM hΓ hlower
    (fun h => hnot ((s.swap_null_iff hΓ).mp h)) ((s.swap_typeA A).mpr ha) hAY
  change ThreePencil M Γ (M.closure (A ∪ s.swap.F₁)) s.Y at hh
  rw [s.swap_first] at hh
  exact hh

theorem second_three_on_W (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAW : A ⊆ s.W) :
    ThreePencil M Γ (M.closure (A ∪ s.F₂)) s.W := by
  have hh := c.flip.first_three_on_W hM hΓ hlower
    (fun h => hnot (s.flip_null_iff.mp h)) ((s.flip_typeA A).mpr ha) hAW
  rw [s.flip_first] at hh
  exact hh

theorem second_three_on_Y (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) (hAY : A ⊆ s.Y) :
    ThreePencil M Γ (M.closure (A ∪ s.F₂)) s.Y := by
  have hh := c.flip.first_three_on_Y hM hΓ hlower
    (fun h => hnot (s.flip_null_iff.mp h)) ((s.flip_typeA A).mpr ha) hAY
  rw [s.flip_first] at hh
  exact hh

theorem cut_above_typeA (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path)
    {A : Set α} (ha : s.TypeA A) :
    ∃ U V, IsHyperplane M U ∧ IsHyperplane M V ∧ A ⊆ U ∧ A ⊆ V ∧
      U ∈ Γ ∧ V ∈ Γ ∧ U ≠ V ∧
      ∀ J, IsHyperplane M J → A ⊆ J → J ∈ Γ → J = U ∨ J = V := by
  rcases typeA_one_side ha with ⟨hw,hny⟩ | ⟨hy,hnw⟩
  · exact c.cut_above_typeA_on_W hM hΓ hlower hnot ha hw hny
  · exact c.swap.cut_above_typeA_on_W hM hΓ hlower
      (fun h => hnot ((s.swap_null_iff hΓ).mp h)) ((s.swap_typeA A).mpr ha) hy hnw
end CountingFrame
end TutteFormalization.Homotopy
