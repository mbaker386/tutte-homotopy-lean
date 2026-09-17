import TutteFormalization.Homotopy.FourPointEmbedding
import TutteFormalization.Homotopy.Elementary

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Full induced-cut recognition for the approved local third-kind model.
The two cut diagonals and four off sides determine every represented flat. -/
theorem exact_thirdCut (φ : ModelEmbedding u34 M) (hΓ : ModularCut M Γ)
    (h12 : φ.image {1,2} ∈ cutPlus M Γ) (h03 : φ.image {0,3} ∈ cutPlus M Γ)
    (h01 : φ.image {0,1} ∉ cutPlus M Γ) (h02 : φ.image {0,2} ∉ cutPlus M Γ)
    (h23 : φ.image {2,3} ∉ cutPlus M Γ) (h13 : φ.image {1,3} ∉ cutPlus M Γ) :
    ExactCut φ Γ thirdCut := by
  let sides : Fin 4 → Finset (Fin 4) := ![{0,1},{0,2},{2,3},{1,3}]
  have hsides : ∀ i, u34.Flat (sides i) := by decide
  have hoff : ∀ i, φ.image (sides i) ∉ cutPlus M Γ := by
    intro i; fin_cases i <;> assumption
  have hclass : ∀ F, u34.Flat F → F ∈ thirdCut ∨ ∃ i, F ⊆ sides i := by decide
  have hcuts : ∀ F, F ∈ thirdCut → F ∈ φ.InducedCut Γ := by
    intro F hF
    have casesF : F = {1,2} ∨ F = {0,3} ∨ F = Finset.univ := by
      simpa only [thirdCut,Finset.mem_insert,Finset.mem_singleton] using hF
    rcases casesF with rfl | rfl | rfl
    · exact ⟨by decide,h12⟩
    · exact ⟨by decide,h03⟩
    · exact ⟨u34.top_flat,by rw [φ.map_top]; exact Or.inr rfl⟩
  ext F
  constructor
  · intro hF
    rcases hclass F hF.1 with hc | ⟨i,hFi⟩
    · exact hc
    · exact False.elim (hoff i ((φ.induced_upward hΓ hF (hsides i) hFi).2))
  · exact hcuts F
end TutteFormalization.Homotopy
