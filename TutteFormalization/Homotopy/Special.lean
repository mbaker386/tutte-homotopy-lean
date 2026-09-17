import TutteFormalization.Homotopy.FourthSpecial
import TutteFormalization.Homotopy.LargeSpecial

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The manuscript's Special Lemma in the connected ambient context needed by
the public homotopy theorem. The higher-corank, original counting/recognition,
and extra-flat branches are all proved without the main theorem. -/
theorem null_of_lower (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 3 ≤ n) (hlower : Lower M Γ n)
    (hrD : natRank M s.D + (n+1) = natRank M M.E) : NullHomotopic M Γ s.path := by
  by_cases he : n = 3
  · subst n
    exact s.null_of_corankFour hM hΓ hlower hrD
  · exact s.null_of_large_corank hM hΓ (by omega) hlower hrD
end TutteFormalization.Homotopy.SpecialData
