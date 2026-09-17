import TutteFormalization.Homotopy.CubeParity

namespace TutteFormalization.Homotopy

/-- The finite incidence count needed by recognition: each of the six labels
is in exactly two selected triple hyperplanes, so there are four selected
hyperplanes. This only counts the supplied incidences; it assumes no cut recognition. -/
theorem cube_degree_count (C : Finset (Fin 8))
    (h : ∀ k : Fin 6, (C.filter (fun i => k ∈ cubeTriple i)).card = 2) : C.card = 4 := by
  have pair : ∀ i : Fin 8, 3 ∈ cubeTriple i ↔ 0 ∉ cubeTriple i := by decide
  have he : C.filter (fun i => 0 ∉ cubeTriple i) = C.filter (fun i => 3 ∈ cubeTriple i) := by
    ext i
    simp only [Finset.mem_filter,pair]
  have hc := Finset.card_filter_add_card_filter_not (s := C) (fun i => 0 ∈ cubeTriple i)
  rw [he,h 0,h 3] at hc
  omega
end TutteFormalization.Homotopy
