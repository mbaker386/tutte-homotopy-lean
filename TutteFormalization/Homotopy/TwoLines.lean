import TutteFormalization.Homotopy.TransversalBelow

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- An indecomposable corank-two flat cannot be contained in a decomposable
flat of the same corank. -/
theorem indec_corankTwo_not_below {L K : Set α} (hL : Indecomposable M L)
    (hcL : CorankTwo M L) (hcK : CorankTwo M K) (hnK : ¬ Indecomposable M K) : ¬ L ⊆ K := by
  intro h
  have hrL := corankTwo_natRank hcL
  have hrK := corankTwo_natRank hcK
  have he := flat_eq_of_subset_of_natRank_le hL.1 hcK.1 h (by omega)
  exact hnK (he ▸ hL)

/-- B.27's count, by injecting lines on W into the two other hyperplanes
above a fixed line on Y. Diamond supplies the lower bound of two. -/
theorem two_lines_of_pencil_count {P W Y : Set α}
    (hP : Indecomposable M P) (hrP : natRank M P + 3 = natRank M M.E)
    (hW : IsHyperplane M W) (hY : IsHyperplane M Y)
    (hPW : P ⊆ W) (hPY : P ⊆ Y)
    (hc : CorankTwo M (W ∩ Y)) (hdec : ¬ Indecomposable M (W ∩ Y))
    (hcount : ∀ L, Indecomposable M L → CorankTwo M L → P ⊆ L → L ⊆ Y →
      ThreePencil M Γ L Y) :
    ∃ L K, Indecomposable M L ∧ Indecomposable M K ∧ CorankTwo M L ∧ CorankTwo M K ∧
      P ⊆ L ∧ P ⊆ K ∧ L ⊆ W ∧ K ⊆ W ∧ L ≠ K ∧
      ∀ J, Indecomposable M J → CorankTwo M J → P ⊆ J → J ⊆ W → J = L ∨ J = K := by
  have hrW := hyperplane_natRank hW
  have hrY := hyperplane_natRank hY
  obtain ⟨L₀,_,hL₀,_,hPL₀,_,hL₀Y,_,_,hrL₀,_⟩ :=
    exists_indecomposable_diamond (hyperplane_indecomposable hY) hP hPY (by omega)
  have hcL₀ : CorankTwo M L₀ := (corankTwo_iff_natRank hL₀.1).mpr (by omega)
  have hnL₀W : ¬ L₀ ⊆ W := fun h => indec_corankTwo_not_below hL₀ hcL₀ hc hdec
    (Set.subset_inter h hL₀Y)
  obtain ⟨H,K,hH,hK,hLH,hLK,hHY,hKY,hHK,_,_,hall⟩ := hcount L₀ hL₀ hcL₀ hPL₀ hL₀Y
  let Lines := {L : Set α // Indecomposable M L ∧ CorankTwo M L ∧ P ⊆ L ∧ L ⊆ W}
  let f (L : Lines) := M.closure (L.val ∪ L₀)
  have hf (L : Lines) : IsHyperplane M (f L) :=
    corankTwo_join_isHyperplane hP.1 hrP L.property.2.1 hcL₀ L.property.2.2.1 hPL₀
      (fun he => hnL₀W (he ▸ L.property.2.2.2))
  have hLf (L : Lines) : L.val ⊆ f L :=
    M.subset_closure_of_subset' Set.subset_union_left L.property.1.1.subset_ground
  have hL₀f (L : Lines) : L₀ ⊆ f L :=
    M.subset_closure_of_subset' Set.subset_union_right hL₀.1.subset_ground
  have hnW (L : Lines) : f L ≠ W := fun he => hnL₀W ((hL₀f L).trans_eq he)
  have hnY (L : Lines) : f L ≠ Y := fun he =>
    indec_corankTwo_not_below L.property.1 L.property.2.1 hc hdec
      (Set.subset_inter L.property.2.2.2 ((hLf L).trans_eq he))
  have trace (L : Lines) : f L ∩ W = L.val :=
    hyperplane_inter_eq_of_corankTwo L.property.2.1 (hf L) hW (hnW L) (hLf L) L.property.2.2.2
  have inj : Function.Injective f := by
    intro L J he
    apply Subtype.ext
    exact (trace L).symm.trans ((congrArg (fun Z => Z ∩ W) he).trans (trace J))
  have cover (L : Lines) : f L = H ∨ f L = K := by
    rcases hall (f L) (hf L) (hL₀f L) with he | he | he
    · exact False.elim (hnY L he)
    · exact Or.inl he
    · exact Or.inr he
  have two : ∃ L J : Lines, L ≠ J := by
    obtain ⟨L,J,hL,hJ,hPL,hPJ,hLW,hJW,hLJ,hrL,hrJ⟩ :=
      exists_indecomposable_diamond (hyperplane_indecomposable hW) hP hPW (by omega)
    have hcL : CorankTwo M L := (corankTwo_iff_natRank hL.1).mpr (by omega)
    have hcJ : CorankTwo M J := (corankTwo_iff_natRank hJ.1).mpr (by omega)
    exact ⟨⟨L,hL,hcL,hPL,hLW⟩,⟨J,hJ,hcJ,hPJ,hJW⟩,fun he => hLJ (congrArg Subtype.val he)⟩
  obtain ⟨L,J,hLJ,_,_,_,_,all⟩ := two_slots_exactly_two (fun L => f L = H) (fun L => f L = K)
    cover (fun x y hx hy => inj (hx.trans hy.symm)) (fun x y hx hy => inj (hx.trans hy.symm)) two
  refine ⟨L.val,J.val,L.property.1,J.property.1,L.property.2.1,J.property.2.1,
    L.property.2.2.1,J.property.2.2.1,L.property.2.2.2,J.property.2.2.2,
    fun he => hLJ (Subtype.ext he),?_⟩
  intro Z hZ hcZ hPZ hZW
  rcases all ⟨Z,hZ,hcZ,hPZ,hZW⟩ with he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (congrArg Subtype.val he)
end TutteFormalization.Homotopy
