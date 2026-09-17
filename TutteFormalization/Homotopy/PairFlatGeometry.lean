import TutteFormalization.Homotopy.SixFlatData
import TutteFormalization.Homotopy.PointRepresentatives
import TutteFormalization.Homotopy.PairPlaneRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

def CountingFrame.pairPlane {s : SpecialData M Γ} (c : CountingFrame s) : Fin 3 → Set α :=
  ![s.W ∩ s.Y,s.W ∩ c.T,s.Y ∩ c.T]

namespace CountingFrame
variable {s : SpecialData M Γ} (c : CountingFrame s)
theorem planes_hyperplane : ∀ i, IsHyperplane M (c.planes i) := by
  intro i; fin_cases i
  · exact c.hT
  · exact s.hY
  · exact s.hW
theorem planes_off : ∀ i, c.planes i ∉ Γ := by
  intro i; fin_cases i
  · exact c.offT
  · exact s.offY
  · exact s.offW
theorem planes_above : ∀ i, s.D ⊆ c.planes i := by
  intro i; fin_cases i
  · exact c.DT
  · exact s.D_subset_Y
  · exact s.D_subset_W
theorem pairPlane_corank : ∀ i, CorankTwo M (c.pairPlane i) := by
  intro i; fin_cases i
  · exact s.middle_corank
  · exact c.corankWT
  · exact c.corankYT
theorem pairPlane_decomp : ∀ i, ¬ Indecomposable M (c.pairPlane i) := by
  intro i; fin_cases i
  · exact s.middle_decomp
  · exact c.decompWT
  · exact c.decompYT
end CountingFrame
namespace SixFlatData
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

theorem pair_subsets (i : Fin 3) :
    d.point ⟨i.val,by omega⟩ ⊆ c.pairPlane i ∧
    d.point ⟨i.val+3,by omega⟩ ⊆ c.pairPlane i := by
  fin_cases i
  · exact ⟨Set.subset_inter ((d.incidence 0 2).mpr (by decide)) ((d.incidence 0 1).mpr (by decide)),
      Set.subset_inter ((d.incidence 3 2).mpr (by decide)) ((d.incidence 3 1).mpr (by decide))⟩
  · exact ⟨Set.subset_inter ((d.incidence 1 2).mpr (by decide)) ((d.incidence 1 0).mpr (by decide)),
      Set.subset_inter ((d.incidence 4 2).mpr (by decide)) ((d.incidence 4 0).mpr (by decide))⟩
  · exact ⟨Set.subset_inter ((d.incidence 2 1).mpr (by decide)) ((d.incidence 2 0).mpr (by decide)),
      Set.subset_inter ((d.incidence 5 1).mpr (by decide)) ((d.incidence 5 0).mpr (by decide))⟩

/-- Each labelled pair generates the corresponding actual decomposable plane. -/
theorem pair_join (i : Fin 3) :
    M.closure (d.point ⟨i.val,by omega⟩ ∪ d.point ⟨i.val+3,by omega⟩) = c.pairPlane i := by
  have hr := corankTwo_natRank (c.pairPlane_corank i)
  have hrD := c.rankD
  apply cover_flats_join_eq (c.pairPlane_corank i).1 (d.indec _).1 (d.indec _).1
    (d.pair_subsets i).1 (d.pair_subsets i).2 (d.rank _) (d.rank _) (by omega)
  intro he
  have hi := congrArg Fin.val (d.injective he)
  simp only at hi
  omega

include d in
theorem pairPlane_above (i : Fin 3) : s.D ⊆ c.pairPlane i :=
  (d.above ⟨i.val,by omega⟩).trans (d.pair_subsets i).1
end SixFlatData
end TutteFormalization.Homotopy
