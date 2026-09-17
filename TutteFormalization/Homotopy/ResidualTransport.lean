import TutteFormalization.Homotopy.ExtraJoinOff

namespace TutteFormalization.Homotopy.CorankThreeStep
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}
variable {s t : CorankThreeStep M Γ D G}

/-- Residual transformations with the same local occurrence count may use
an already checked easy case, without any recursive Special invocation. -/
theorem reduced_of_homotopic (hh : Homotopic M Γ s.path t.path)
    (hc : outsideCount t.path G ≤ outsideCount s.path G) (ht : t.Reduced) : s.Reduced := by
  obtain ⟨q,hq,hqD,hlt⟩ := ht
  exact ⟨q,hh.trans hq,hqD,lt_of_lt_of_le hlt hc⟩

/-- Adding an on-G prefix to a reduced residual configuration does not add
outside occurrences. Endpoint and On/Off facts come from the actual paths. -/
theorem reduced_of_good_prefix (a : TuttePath M) (haD : a.On D) (haG : a.On G)
    (haOff : a.Off (cutPlus M Γ)) (hat : a.terminus = t.path.origin)
    (hh : Homotopic M Γ s.path (a.concat t.path hat))
    (hc : outsideCount t.path G ≤ outsideCount s.path G) (ht : t.Reduced) : s.Reduced := by
  classical
  obtain ⟨q,hq,hqD,hlt⟩ := ht
  have haq := hat.trans hq.endpoints.1
  have ha0 := (outsideCount_zero_iff a G).mpr haG
  have hGq : G ⊆ q.origin := t.goodH.trans_eq hq.endpoints.1
  have hcount := outsideCount_concat a q haq G
  simp only [ha0,if_pos hGq,Nat.add_zero,Nat.zero_add] at hcount
  refine ⟨a.concat q haq,hh.trans (hq.prepend a haOff hat),TuttePath.concat_on haD hqD haq,?_⟩
  rw [hcount]
  exact lt_of_lt_of_le hlt hc

/-- Apply either the preliminary below-H triangle or the U-off four-triangle
case for any actual selected candidate P. Used in all residual reductions. -/
theorem reduced_of_candidate_off (s : CorankThreeStep M Γ D G)
    (hΓ : ModularCut M Γ) (hD : M.IsFlat D) (hG : Indecomposable M G)
    (hDG : D ⊆ G) (hrG : natRank M G = natRank M D + 1) (hZΓ : s.Z ∈ Γ)
    {P : Set α} (hP : Indecomposable M P) (hcP : CorankTwo M P)
    (hFP : s.F ⊆ P) (hPJ : P ⊆ s.J) (hPQ : P ≠ s.K ∩ s.J)
    (ho : M.closure ((s.H ∩ s.K) ∪ P) ∉ Γ) : s.Reduced := by
  by_cases hPH : P ⊆ s.H
  · exact s.reduced_of_cover_below hΓ hP hcP hPH hPJ
  · let c : SelectedCover s := ⟨P,hP,hcP,hFP,hPJ,hPQ,hPH⟩
    exact c.reduced_of_U_off hΓ hD hG hDG hrG hZΓ ho
end TutteFormalization.Homotopy.CorankThreeStep
