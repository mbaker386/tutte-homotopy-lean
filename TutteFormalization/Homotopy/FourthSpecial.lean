import TutteFormalization.Homotopy.SixModelPath
import TutteFormalization.Homotopy.FourthRecognition

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}
namespace SixFlatData
variable {s : SpecialData M Γ} {c : CountingFrame s} (d : SixFlatData c)

include d in
/-- B.28 with every actual ambient model/cut/path recognition premise supplied
from the manuscript's counts. No extra elementary constructor is introduced. -/
theorem original_path_elementary (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hnot : ¬ NullHomotopic M Γ s.path) : Elementary M Γ s.path := by
  obtain ⟨x,y,hxy,hw⟩ := d.original_path_word
  exact fourth_elementary_of_count d.ambientModel hΓ (fun _ h => d.circuit_off h)
    (fun i => by rw [d.ambientModel_pair]; exact c.pairPlane_decomp i)
    d.cutTriples d.mem_cutTriples (d.cutTriples_card_four hM hΓ hlower hnot) x y hxy s.path hw
    (TuttePath.square_closed _ _ _ _ _ _ _ _)
    ((off_cutPlus _).mpr (TuttePath.square_off _ _ _ _ _ _ _ _ s.offW s.offX s.offY s.offZ))
end SixFlatData
namespace SpecialData

theorem null_of_corankFour (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    (hlower : Lower M Γ 3) (hrD : natRank M s.D + 4 = natRank M M.E) :
    NullHomotopic M Γ s.path := by
  by_contra hn
  obtain ⟨c⟩ := s.exists_countingFrame hM hΓ hlower hrD hn
  obtain ⟨d⟩ := c.exists_sixFlatData hM hΓ hlower hn
  exact hn (elementary_null (d.original_path_elementary hM hΓ hlower hn))
end SpecialData
end TutteFormalization.Homotopy
