import TutteFormalization.Homotopy.CutBranchEdges
import TutteFormalization.Homotopy.TriangleExchange

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The four actual triangle moves in the U-off part of 2.2.2. Their
carriers are checked separately before the two contextual exchanges. -/
theorem four_triangle_shortcut (hΓ : ModularCut M Γ) {D G F P H K J U V : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (hU : IsHyperplane M U) (hV : IsHyperplane M V)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hHU : TutteAdjacent M H U) (hKU : TutteAdjacent M K U) (hUJ : TutteAdjacent M U J)
    (hUV : TutteAdjacent M U V) (hVJ : TutteAdjacent M V J) (hVH : TutteAdjacent M V H)
    (hF : F = H ∩ K ∩ J) (hrF : natRank M F + 3 = natRank M M.E)
    (hAU : H ∩ K ⊆ U) (hP : CorankTwo M P) (hFP : F ⊆ P)
    (hPU : P ⊆ U) (hPV : P ⊆ V) (hPJ : P ⊆ J) (hPH : ¬ P ⊆ H)
    (hoH : H ∉ Γ) (hoK : K ∉ Γ) (hoJ : J ∉ Γ) (hoU : U ∉ Γ) (hoV : V ∉ Γ)
    (hDH : D ⊆ H) (hDJ : D ⊆ J) (hDV : D ⊆ V) (hGV : G ⊆ V) (hGK : ¬ G ⊆ K) :
    ∃ q : TuttePath M,
      Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) q ∧
      q.On D ∧ outsideCount q G <
        outsideCount ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl) G := by
  have hFflat : M.IsFlat F := hF.symm ▸ flat_inter (flat_inter hH.1 hK.1) hJ.1
  have hFH : F ⊆ H := hF ▸ (fun _ hx => hx.1.1)
  have hrP := corankTwo_natRank hP
  have hKUeq : K ∩ U = H ∩ K := hyperplane_inter_eq_of_corankTwo hHK.2.2 hK hU hKU.1
    Set.inter_subset_right hAU
  have ht1 : K ∩ U ∩ J = F := by rw [hKUeq,← hF]
  have hUVeq : U ∩ V = P := hyperplane_inter_eq_of_corankTwo hP hU hV hUV.1 hPU hPV
  have hPHeq := (hyperplane_inter_of_cover hFflat hP.1 hH hFP hFH (by omega) hPH).1
  have ht2 : H ∩ U ∩ V = F := by
    rw [Set.inter_assoc,hUVeq,Set.inter_comm H P,hPHeq]
  have t1 := triangle_shortcut hΓ hH hK hU hHK hKU hHU.symm
    (elementary_null (triangle_rankTwo_elementary hΓ hHK.2.2 hH hK hU hHK hKU hHU.symm
      Set.inter_subset_left Set.inter_subset_right hAU hoH hoK hoU))
  have t2 := triangle_shortcut hΓ hK hU hJ hKU hUJ hKJ.symm
    (elementary_null (triangle_rankThree_elementary hΓ hK hU hJ hKU hUJ hKJ.symm
      (by rw [ht1]; exact hrF) hoK hoU hoJ))
  have t3 := triangle_shortcut hΓ hH hU hV hHU hUV hVH
    (elementary_null (triangle_rankThree_elementary hΓ hH hU hV hHU hUV hVH
      (by rw [ht2]; exact hrF) hoH hoU hoV))
  have t4 := triangle_shortcut hΓ hU hV hJ hUV hVJ hUJ.symm
    (elementary_null (triangle_rankTwo_elementary hΓ hP hU hV hJ hUV hVJ hUJ.symm
      hPU hPV hPJ hoU hoV hoJ))
  have ha := triangle_exchange hH hK hJ hU hHK hKJ hHU hKU hUJ t1 t2
  have hb := triangle_exchange hH hU hJ hV hHU hUJ hVH.symm hUV hVJ t3 t4
  exact ⟨(TuttePath.edge hH hV hVH.symm).concat (TuttePath.edge hV hJ hVJ) rfl,
    ha.trans hb,TuttePath.concat_on (TuttePath.edge_on _ _ _ hDH hDV)
      (TuttePath.edge_on _ _ _ hDV hDJ) rfl,
    twoEdge_count_decreases hH hK hJ hV hHK hKJ hVH.symm hVJ hGV hGK⟩
end TutteFormalization.Homotopy
