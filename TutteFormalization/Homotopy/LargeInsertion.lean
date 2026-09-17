import TutteFormalization.Homotopy.SquareInsertion
import TutteFormalization.Homotopy.TriangleRankThree

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite] {Γ : Set (Set α)} {D G : Set α}

/-- Actual local insertion certificates for Case 2.3, including the retained
bad penultimate vertex and containment of the raised flat in its triple. -/
def LargeCorankStep.Inserted (s : LargeCorankStep M Γ D G) (P : Set α) (q : TuttePath M) : Prop :=
  Homotopic M Γ s.path q ∧ q.On D ∧ outsideCount q G = outsideCount s.path G ∧
  3 ≤ q.length ∧
  (∀ j : Fin (q.length+1), j.val < q.length-1 → G ⊆ q.vertex j) ∧
  (¬ G ⊆ q.vertex ⟨q.length-1,by omega⟩) ∧
  P ⊆ q.vertex ⟨q.length-2,by omega⟩ ∧
  P ⊆ q.vertex ⟨q.length-1,by omega⟩ ∧ P ⊆ q.vertex (Fin.last q.length)

namespace LargeBridge
variable {s : LargeCorankStep M Γ D G} (b : LargeBridge M Γ s)

/-- Indecomposable L': the source triangle inserts T' before the first offender. -/
theorem insert_indec (hΓ : ModularCut M Γ) (hi : Indecomposable M (b.T ∩ s.B)) :
    ∃ q, s.Inserted b.P q := by
  let hTB : TutteAdjacent M b.T s.B := ⟨b.neB,hi,b.corankTB⟩
  have htr : s.H ∩ b.T ∩ s.B = b.K := by
    calc
      _ = s.H ∩ s.B ∩ b.T := by ext x; simp only [Set.mem_inter_iff]; tauto
      _ = b.K := b.triple
  have hs := triangle_shortcut hΓ s.hH b.hT s.hB b.hHT hTB s.hHB.symm
    (elementary_null (triangle_rankThree_elementary hΓ s.hH b.hT s.hB b.hHT hTB s.hHB.symm
      (htr.symm ▸ b.rankK) s.offH b.offT s.offB))
  let q := (TuttePath.edge s.hH b.hT b.hHT).concat
    ((TuttePath.edge b.hT s.hB hTB).concat (TuttePath.edge s.hB s.hJ s.hBJ) rfl) rfl
  have hh := hs.symm.append (TuttePath.edge s.hB s.hJ s.hBJ)
    ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ s.offB s.offJ)) rfl
  have heq : ((TuttePath.edge s.hH b.hT b.hHT).concat (TuttePath.edge b.hT s.hB hTB) rfl).concat
      (TuttePath.edge s.hB s.hJ s.hBJ) rfl = q := by apply TuttePath.eq_of_word_eq; rfl
  refine ⟨q,heq ▸ hh,?_,?_,by change 3 ≤ 3; decide,?_,s.badB,b.PT,b.belowP.trans Set.inter_subset_left,
    b.belowP.trans Set.inter_subset_right⟩
  · intro j; fin_cases j
    · exact s.onH
    · exact b.D_subset_P.trans b.PT
    · exact s.onB
    · exact s.onJ
  · classical
    rw [outsideCount_word,outsideCount_word]
    change [s.H,b.T,s.B,s.J].countP _ = [s.H,s.B,s.J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [b.goodT]
  · intro j hj
    change j.val < 2 at hj
    fin_cases j
    · exact s.goodH
    · exact b.goodT
    · change 2 < 2 at hj; omega
    · change 3 < 2 at hj; omega

/-- Decomposable L': the proved special square inserts T',U before B. -/
theorem insert_decomp (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ}
    (hlower : Lower M Γ n) (hG : Indecomposable M G) (hDG : D ⊆ G)
    (hrG : natRank M G = natRank M D + 1) (hrD : natRank M M.E - natRank M D ≤ n+1)
    (hi : ¬ Indecomposable M (b.T ∩ s.B)) : ∃ q, s.Inserted b.P q := by
  obtain ⟨U,hU,hTU,hUB,hoU,hGU,hPU,hn⟩ := b.exists_special_insertion hM hΓ hlower hG hDG hrG hrD hi
  have hs := square_insertion hΓ s.hH b.hT hU s.hB b.hHT hTU hUB s.hHB hn
  let q := (TuttePath.edge s.hH b.hT b.hHT).concat
    ((TuttePath.edge b.hT hU hTU).concat
      ((TuttePath.edge hU s.hB hUB).concat (TuttePath.edge s.hB s.hJ s.hBJ) rfl) rfl) rfl
  have hh := hs.append (TuttePath.edge s.hB s.hJ s.hBJ)
    ((off_cutPlus _).mpr (TuttePath.edge_off _ _ _ s.offB s.offJ)) rfl
  have heq : ((TuttePath.edge s.hH b.hT b.hHT).concat
      ((TuttePath.edge b.hT hU hTU).concat (TuttePath.edge hU s.hB hUB) rfl) rfl).concat
      (TuttePath.edge s.hB s.hJ s.hBJ) rfl = q := by apply TuttePath.eq_of_word_eq; rfl
  refine ⟨q,heq ▸ hh,?_,?_,by change 3 ≤ 4; decide,?_,s.badB,hPU,b.belowP.trans Set.inter_subset_left,
    b.belowP.trans Set.inter_subset_right⟩
  · intro j; fin_cases j
    · exact s.onH
    · exact b.D_subset_P.trans b.PT
    · exact hDG.trans hGU
    · exact s.onB
    · exact s.onJ
  · classical
    rw [outsideCount_word,outsideCount_word]
    change [s.H,b.T,U,s.B,s.J].countP _ = [s.H,s.B,s.J].countP _
    simp only [List.countP_cons,List.countP_nil]
    simp [b.goodT,hGU]
  · intro j hj
    change j.val < 3 at hj
    fin_cases j
    · exact s.goodH
    · exact b.goodT
    · exact hGU
    · change 3 < 3 at hj; omega
    · change 4 < 3 at hj; omega
end LargeBridge

/-- Both local branches of source Case 2.3 with their exact rank improvement. -/
theorem LargeCorankStep.exists_insertion (s : LargeCorankStep M Γ D G)
    (hM : Connected M) (hΓ : ModularCut M Γ) {n : ℕ} (hlower : Lower M Γ n)
    (hD : M.IsFlat D) (hG : Indecomposable M G) (hDG : D ⊆ G)
    (hrG : natRank M G = natRank M D + 1) (hrD : natRank M M.E - natRank M D ≤ n+1) :
    ∃ P q, natRank M P = natRank M s.F + 1 ∧ s.Inserted P q := by
  classical
  obtain ⟨b⟩ := s.exists_bridge hΓ hD hG hDG hrG
  obtain ⟨q,hq⟩ : ∃ q, s.Inserted b.P q := by
    by_cases hi : Indecomposable M (b.T ∩ s.B)
    · exact b.insert_indec hΓ hi
    · exact b.insert_decomp hM hΓ hlower hG hDG hrG hrD hi
  exact ⟨b.P,q,b.rankP,hq⟩
end TutteFormalization.Homotopy
