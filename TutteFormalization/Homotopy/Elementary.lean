import TutteFormalization.Homotopy.Embedding
import TutteFormalization.Homotopy.PathCalculus

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} [M.Finite]

/-- Complete inverse-image equality on ALL selected flats, not only hyperplanes. -/
def ExactCut {n} {N : FiniteModel n} (φ : ModelEmbedding N M)
    (Γ : Set (Set α)) (C : Finset (Finset (Fin n))) : Prop := φ.InducedCut Γ = C

/-- S4: precisely the five labelled presentations of the four BJL kinds.
All indices are zero-based: {0,1} means manuscript flat 12. Each p is already
an ambient valid TuttePath; its Off and Closed certificates are explicit.
Arbitrary squares and recognition hypotheses are not constructors. -/
inductive BaseElementary (M : Matroid α) [M.Finite] (Γ : Set (Set α)) : TuttePath M → Prop
  | first (φ : ModelEmbedding u22 M) (p : TuttePath M)
      (cut : ExactCut φ Γ {Finset.univ}) (bottom : Indecomposable M (φ.image ∅))
      (word : p.word = [{0}, {1}, {0}].map φ.image)
      (closed : Closed p) (off : p.Off (cutPlus M Γ)) : BaseElementary M Γ p
  | secondA (φ : ModelEmbedding u23 M) (p : TuttePath M)
      (cut : ExactCut φ Γ {Finset.univ})
      (word : p.word = [{0}, {1}, {2}, {0}].map φ.image)
      (closed : Closed p) (off : p.Off (cutPlus M Γ)) : BaseElementary M Γ p
  | secondB (φ : ModelEmbedding u33 M) (p : TuttePath M)
      (cut : ExactCut φ Γ {Finset.univ})
      (points : ∀ i : Fin 3, Indecomposable M (φ.image {i}))
      (word : p.word = [{0,1}, {0,2}, {1,2}, {0,1}].map φ.image)
      (closed : Closed p) (off : p.Off (cutPlus M Γ)) : BaseElementary M Γ p
  | third (φ : ModelEmbedding u34 M) (p : TuttePath M)
      (cut : ExactCut φ Γ thirdCut)
      (word : p.word = [{0,1}, {0,2}, {2,3}, {1,3}, {0,1}].map φ.image)
      (closed : Closed p) (off : p.Off (cutPlus M Γ)) : BaseElementary M Γ p
  | fourth (φ : ModelEmbedding bipartiteModel M) (p : TuttePath M)
      (cut : ExactCut φ Γ fourthCut)
      (pair14 : ¬ Indecomposable M (φ.image {0,3}))
      (pair25 : ¬ Indecomposable M (φ.image {1,4}))
      (pair36 : ¬ Indecomposable M (φ.image {2,5}))
      (word : p.word = [{0,1,3,4}, {0,1,5}, {0,2,3,5}, {3,4,5}, {0,1,3,4}].map φ.image)
      (closed : Closed p) (off : p.Off (cutPlus M Γ)) : BaseElementary M Γ p

/-- All embeddings supply permitted labellings; these constructors add only
reversal and cyclic rotation, implemented as exchange of two matching segments. -/
inductive Elementary (M : Matroid α) [M.Finite] (Γ : Set (Set α)) : TuttePath M → Prop
  | base {p} : BaseElementary M Γ p → Elementary M Γ p
  | reverse {p} : Elementary M Γ p → Elementary M Γ p.reverse
  | rotate {a b : TuttePath M} (hab : a.terminus = b.origin) (hba : b.terminus = a.origin)
      (offa : a.Off (cutPlus M Γ)) (offb : b.Off (cutPlus M Γ)) :
      Elementary M Γ (a.concat b hab) → Elementary M Γ (b.concat a hba)

theorem BaseElementary.closed {Γ} {p : TuttePath M} (h : BaseElementary M Γ p) : Closed p := by
  cases h <;> assumption

theorem BaseElementary.off {Γ} {p : TuttePath M} (h : BaseElementary M Γ p) :
    p.Off (cutPlus M Γ) := by cases h <;> assumption

theorem Elementary.closed {Γ} {p : TuttePath M} (h : Elementary M Γ p) : Closed p := by
  induction h with
  | base h => exact h.closed
  | reverse h ih => simpa [Closed] using ih.symm
  | rotate hab hba ha hb h ih => simpa [Closed] using hab.symm

theorem Elementary.off {Γ} {p : TuttePath M} (h : Elementary M Γ p) :
    p.Off (cutPlus M Γ) := by
  induction h with
  | base h => exact h.off
  | reverse h ih => exact TuttePath.reverse_off ih
  | rotate hab hba ha hb h ih => exact TuttePath.concat_off hb ha hba
end TutteFormalization.Homotopy
