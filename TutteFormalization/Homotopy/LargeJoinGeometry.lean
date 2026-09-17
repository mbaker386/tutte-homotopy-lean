import TutteFormalization.Homotopy.LargeComplement

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- Case 2.3's T'=L∨P and L'=K∨P, where P is the Complement flat F'.
All rank, Off, distinctness and intersection certificates used by either
branch are derived before constructing a deformation. -/
theorem large_join_geometry {F G K P L H B J T : Set α}
    (hF : M.IsFlat F) (hK : M.IsFlat K) (hrK : natRank M K + 3 = natRank M M.E)
    (hFK : F ⊆ K) (hKA : K ⊆ H ∩ B) (hKL : K ⊆ L)
    (hL : CorankTwo M L) (hLH : L ⊆ H) (hGL : G ⊆ L) (hGB : ¬ G ⊆ B)
    (hP : M.IsFlat P) (hFP : F ⊂ P) (hPQ : P ⊆ B ∩ J) (hrP : natRank M P = natRank M F + 1)
    (hFeq : F = H ∩ B ∩ J) (hH : IsHyperplane M H) (hB : IsHyperplane M B)
    (hT : IsHyperplane M T) (hLT : L ⊆ T) (hTH : T ≠ H) (hPT : M.closure (P ∪ T) = M.E)
    (preferred : ∀ Q, IsHyperplane M Q → L ⊆ Q → Q ≠ T → Q ∉ Γ) :
    let T' := M.closure (L ∪ P)
    let L' := M.closure (K ∪ P)
    IsHyperplane M T' ∧ T' ≠ H ∧ T' ≠ T ∧ T' ≠ B ∧ T' ∉ Γ ∧
      Indecomposable M L ∧ CorankTwo M L' ∧ L' ⊆ T' ∧ L' ⊆ B ∧
      H ∩ B ∩ T' = K ∧ T' ∩ B = L' := by
  dsimp only
  let T' := M.closure (L ∪ P)
  let L' := M.closure (K ∪ P)
  have hFQ : F ⊆ B ∩ J := by rw [hFeq]; exact fun _ hx => ⟨hx.1.2,hx.2⟩
  have hFL : F ⊆ L := hFK.trans hKL
  have hLQ : L ∩ (B ∩ J) = F := Set.Subset.antisymm
    (by rw [hFeq]; exact fun _ hx => ⟨⟨hLH hx.1,hx.2.1⟩,hx.2.2⟩) (Set.subset_inter hFL hFQ)
  have hPh : ¬ P ⊆ H := by
    intro hh
    apply hFP.2
    rw [hFeq]
    exact fun _ hx => ⟨⟨hh hx,(hPQ hx).1⟩,(hPQ hx).2⟩
  have hT' : IsHyperplane M T' := path_join_isHyperplane hL hP hLQ hFP hPQ hrP
  have hLT' : L ⊆ T' := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
  have hPT' : P ⊆ T' := M.subset_closure_of_subset' Set.subset_union_right hP.subset_ground
  have hneH : T' ≠ H := fun he => hPh (hPT'.trans_eq he)
  have hneT : T' ≠ T := by
    intro he
    have hsub : P ⊆ T := hPT'.trans_eq he
    rw [Set.union_eq_right.mpr hsub,hT.1.closure] at hPT
    exact hT.2.1 hPT
  have hneB : T' ≠ B := fun he => hGB ((hGL.trans hLT').trans_eq he)
  have hiL : Indecomposable M L := (corankTwo_indecomposable_iff_three hL).mpr
    ⟨H,T,T',hH,hT,hT',hTH.symm,hneH.symm,hneT.symm,hLH,hLT,hLT'⟩
  have hnPK : ¬ P ⊆ K := fun hh => hPh (hh.trans (hKA.trans Set.inter_subset_left))
  have hrr := (cover_join_rank hF hP hK hFP.1 hFK hrP hnPK).2
  have hrL' : natRank M L' + 2 = natRank M M.E := by
    have hh : natRank M L' = natRank M K + 1 := by simpa only [Set.union_comm] using hrr
    omega
  have hcL' : CorankTwo M L' := (corankTwo_iff_natRank (M.isFlat_closure _)).mpr hrL'
  have hL'T' : L' ⊆ T' := (M.closure_mono (Set.union_subset (hKL.trans hLT') hPT')).trans_eq hT'.1.closure
  have hL'B : L' ⊆ B := (M.closure_mono (Set.union_subset (hKA.trans Set.inter_subset_right)
    (hPQ.trans Set.inter_subset_left))).trans_eq hB.1.closure
  have hrL := corankTwo_natRank hL
  have hLB := (hyperplane_inter_of_cover hK hL.1 hB hKL (hKA.trans Set.inter_subset_right)
    (by omega) (fun hh => hGB (hGL.trans hh))).1
  have hHT' := hyperplane_inter_eq_of_corankTwo hL hH hT' hneH.symm hLH hLT'
  refine ⟨hT',hneH,hneT,hneB,preferred T' hT' hLT' hneT,hiL,hcL',hL'T',hL'B,?_,
    hyperplane_inter_eq_of_corankTwo hcL' hT' hB hneB hL'T' hL'B⟩
  calc
    H ∩ B ∩ T' = (H ∩ T') ∩ B := by ext x; simp only [Set.mem_inter_iff]; tauto
    _ = K := by rw [hHT',hLB]
end TutteFormalization.Homotopy
