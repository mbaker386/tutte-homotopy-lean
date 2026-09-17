import TutteFormalization.Homotopy.ResidualOutsideGeometry

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)}

/-- The literal five-triangle deformation displayed in residual 2.2.2.4.
Every triangle's nullity is supplied by its checked model recognition. -/
theorem five_triangle_exchange (hΓ : ModularCut M Γ) {H K J W₁ W₂ W₃ : Set α}
    (hH : IsHyperplane M H) (hK : IsHyperplane M K) (hJ : IsHyperplane M J)
    (h1 : IsHyperplane M W₁) (h2 : IsHyperplane M W₂) (h3 : IsHyperplane M W₃)
    (hHK : TutteAdjacent M H K) (hKJ : TutteAdjacent M K J)
    (hH3 : TutteAdjacent M H W₃) (h3K : TutteAdjacent M W₃ K)
    (hK2 : TutteAdjacent M K W₂) (h2J : TutteAdjacent M W₂ J)
    (h32 : TutteAdjacent M W₃ W₂) (h31 : TutteAdjacent M W₃ W₁)
    (h12 : TutteAdjacent M W₁ W₂) (hH1 : TutteAdjacent M H W₁)
    (n1 : NullHomotopic M Γ (TuttePath.triangle hH h3 hK hH3 h3K hHK.symm))
    (n2 : NullHomotopic M Γ (TuttePath.triangle hK h2 hJ hK2 h2J hKJ.symm))
    (n3 : NullHomotopic M Γ (TuttePath.triangle h3 hK h2 h3K hK2 h32.symm))
    (n4 : NullHomotopic M Γ (TuttePath.triangle h3 h1 h2 h31 h12 h32.symm))
    (n5 : NullHomotopic M Γ (TuttePath.triangle hH h3 h1 hH3 h31 hH1.symm)) :
    Homotopic M Γ ((TuttePath.edge hH hK hHK).concat (TuttePath.edge hK hJ hKJ) rfl)
      ((TuttePath.edge hH h1 hH1).concat
        ((TuttePath.edge h1 h2 h12).concat (TuttePath.edge h2 hJ h2J) rfl) rfl) := by
  let a := TuttePath.edge hH h3 hH3
  let b := TuttePath.edge h3 hK h3K
  let c := TuttePath.edge hK h2 hK2
  let d := TuttePath.edge h2 hJ h2J
  let e := TuttePath.edge h3 h2 h32
  let f := TuttePath.edge h3 h1 h31
  let g := TuttePath.edge h1 h2 h12
  let j := TuttePath.edge hH h1 hH1
  let x := TuttePath.edge hH hK hHK
  let y := TuttePath.edge hK hJ hKJ
  have t1 : Homotopic M Γ (a.concat b rfl) x := triangle_shortcut hΓ hH h3 hK hH3 h3K hHK.symm n1
  have t2 : Homotopic M Γ (c.concat d rfl) y := triangle_shortcut hΓ hK h2 hJ hK2 h2J hKJ.symm n2
  have t3 : Homotopic M Γ (b.concat c rfl) e := triangle_shortcut hΓ h3 hK h2 h3K hK2 h32.symm n3
  have t4 : Homotopic M Γ (f.concat g rfl) e := triangle_shortcut hΓ h3 h1 h2 h31 h12 h32.symm n4
  have t5 : Homotopic M Γ (a.concat f rfl) j := triangle_shortcut hΓ hH h3 h1 hH3 h31 hH1.symm n5
  have ha := (t1.symm.append y t2.off.2 rfl).trans (t2.symm.prepend (a.concat b rfl) t1.off.1 rfl)
  have haOff : a.Off (cutPlus M Γ) := TuttePath.off_of_concat_left rfl t1.off.1
  have hdOff : d.Off (cutPlus M Γ) := TuttePath.off_of_concat_right rfl t2.off.1
  have hb := (t3.append d hdOff rfl).prepend a haOff rfl
  have he1 : (a.concat b rfl).concat (c.concat d rfl) rfl = a.concat ((b.concat c rfl).concat d rfl) rfl := by
    apply TuttePath.eq_of_word_eq; rfl
  have hAB : Homotopic M Γ (x.concat y rfl) (a.concat (e.concat d rfl) rfl) := ha.trans (he1.symm ▸ hb)
  have hc := (t4.symm.append d hdOff rfl).prepend a haOff rfl
  have hd := t5.append (g.concat d rfl)
    (TuttePath.concat_off (TuttePath.off_of_concat_right rfl t4.off.1) hdOff rfl) rfl
  have he2 : a.concat ((f.concat g rfl).concat d rfl) rfl = (a.concat f rfl).concat (g.concat d rfl) rfl := by
    apply TuttePath.eq_of_word_eq; rfl
  exact (hAB.trans hc).trans (he2.symm ▸ hd)
end TutteFormalization.Homotopy
