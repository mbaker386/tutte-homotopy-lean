import TutteFormalization.Homotopy.SpecialCorankFour
import TutteFormalization.Homotopy.ThirdFlatConstruction
import TutteFormalization.Homotopy.TwoHalves

namespace TutteFormalization.Homotopy.SpecialData
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- B.23: special paths of carrier corank at least five are null under the
same-ambient Lower premise. The source's Complement and two-filling route is retained. -/
theorem null_of_large_corank (s : SpecialData M Γ) (hM : Connected M) (hΓ : ModularCut M Γ)
    {n : ℕ} (hn : 4 ≤ n) (hlower : Lower M Γ n)
    (hrD : natRank M s.D + (n+1) = natRank M M.E) : NullHomotopic M Γ s.path := by
  by_contra hnot
  obtain ⟨A,B,C,ha,hAW,hnAY,hb,hc,hAB,hAC,hoB,hiB,hiC,hoC,hBC,hinter⟩ :=
    s.exists_opposite_poles hM hΓ (by omega) hlower hrD hnot
  obtain ⟨G,I,hG,hDG,hGF,hGr,hIeq,hI,hIo,hdW,hdY,hj₁,hj₂⟩ :=
    s.exists_corankFour_choice hM hΓ (by omega) hlower hrD hnot
      ha hb hc hAW hAB hAC hBC hinter hoB hiB hiC hoC
  have hGI : G ⊆ I := hIeq ▸
    M.subset_closure_of_subset' Set.subset_union_left hG.1.subset_ground
  obtain ⟨K,Q,hK,hDK,hKF,hKr,hQ,hGQ,hKQ,hQm,hQr⟩ :=
    s.exists_third_flat hG hDG hGF.subset hGr hI hGI hdW.1 hdY.1 hj₁ hj₂
  have hproper : Q ≠ M.E := by
    intro heq
    have hEW : M.E ⊆ s.W := heq ▸ (hQm.trans Set.inter_subset_left)
    exact s.hW.2.1 (Set.Subset.antisymm s.hW.1.subset_ground hEW)
  obtain ⟨e,heY,heW,heQ,heo⟩ := path_theorem M hM Γ hΓ Q hQ hproper
    s.Y s.W s.hY s.hW (hQm.trans Set.inter_subset_right) (hQm.trans Set.inter_subset_left)
    s.offY s.offW
  let a := (TuttePath.edge s.hW s.hX s.hWX).concat (TuttePath.edge s.hX s.hY s.hXY) rfl
  let b := (TuttePath.edge s.hY s.hZ s.hYZ).concat (TuttePath.edge s.hZ s.hW s.hZW) rfl
  have haOff : a.Off Γ := TuttePath.concat_off (TuttePath.edge_off _ _ _ s.offW s.offX)
    (TuttePath.edge_off _ _ _ s.offX s.offY) rfl
  have hbOff : b.Off Γ := TuttePath.concat_off (TuttePath.edge_off _ _ _ s.offY s.offZ)
    (TuttePath.edge_off _ _ _ s.offZ s.offW) rfl
  have haG : a.On G := TuttePath.concat_on
    (TuttePath.edge_on _ _ _ (hGF.subset.trans (fun _ h => h.1.1)) (hGF.subset.trans (fun _ h => h.1.2)))
    (TuttePath.edge_on _ _ _ (hGF.subset.trans (fun _ h => h.1.2)) (hGF.subset.trans Set.inter_subset_right)) rfl
  have hbK : b.On K := TuttePath.concat_on
    (TuttePath.edge_on _ _ _ (hKF.trans (fun _ h => h.1.1)) (hKF.trans (fun _ h => h.1.2)))
    (TuttePath.edge_on _ _ _ (hKF.trans (fun _ h => h.1.2)) (hKF.trans Set.inter_subset_right)) rfl
  have hnull := Lower.null_of_two_halves hΓ hlower a b e.reverse rfl rfl
    ((show a.origin = s.W from rfl).trans (heW.symm.trans (TuttePath.reverse_origin e).symm))
    ((show a.terminus = s.Y from rfl).trans (heY.symm.trans (TuttePath.reverse_terminus e).symm)) haOff hbOff (TuttePath.reverse_off heo)
    haG (TuttePath.reverse_on (fun i => hGQ.trans (heQ i))) hbK
    (TuttePath.reverse_on (fun i => hKQ.trans (heQ i))) (by omega) (by omega)
  apply hnot
  simpa only [path,TuttePath.square_split] using hnull
end TutteFormalization.Homotopy.SpecialData
