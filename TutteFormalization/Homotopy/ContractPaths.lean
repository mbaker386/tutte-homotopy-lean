import TutteFormalization.Homotopy.ContractGeometry
import TutteFormalization.Homotopy.Carrier

namespace TutteFormalization
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {D : Set α}
namespace Homotopy

theorem adjacent_union_contract (hD : M.IsFlat D) {H K : Set α}
    (hH : (M ／ D).IsFlat H) (hK : (M ／ D).IsFlat K)
    (he : TutteAdjacent (M ／ D) H K) : TutteAdjacent M (H ∪ D) (K ∪ D) := by
  have hi : (H ∪ D) ∩ (K ∪ D) = (H ∩ K) ∪ D := by tauto_set
  refine ⟨fun h => he.1 ((union_eq_union_iff hH.subset_ground hK.subset_ground).mp h),?_,?_⟩
  · rw [hi]
    exact (indecomposable_union_contract_iff hD he.2.1.1).mpr he.2.1
  · rw [hi]
    exact corankTwo_union_contract hD he.2.2
end Homotopy
namespace TuttePath

/-- Forward path transport from M/D; every lifted vertex contains D. -/
def liftContraction (p : TuttePath (M ／ D)) (hD : M.IsFlat D) : TuttePath M where
  length := p.length
  vertex i := p.vertex i ∪ D
  isHyperplane i := hyperplane_union_of_contract hD (p.isHyperplane i)
  adjacent i := Homotopy.adjacent_union_contract hD (p.isHyperplane i.castSucc).1
    (p.isHyperplane i.succ).1 (p.adjacent i)

@[simp] theorem liftContraction_origin (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    (p.liftContraction hD).origin = p.origin ∪ D := rfl
@[simp] theorem liftContraction_terminus (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    (p.liftContraction hD).terminus = p.terminus ∪ D := rfl

theorem liftContraction_on (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    (p.liftContraction hD).On D := fun _ => Set.subset_union_right

theorem liftContraction_off_iff (p : TuttePath (M ／ D)) (hD : M.IsFlat D)
    (Γ : Set (Set α)) : (p.liftContraction hD).Off Γ ↔ p.Off (Homotopy.contractionCut M D Γ) := by
  simp only [Off,liftContraction,Homotopy.contractionCut,Set.mem_setOf_eq,
    fun i => (p.isHyperplane i).1,true_and]

theorem liftContraction_off_normalized (p : TuttePath (M ／ D)) (hD : M.IsFlat D)
    {Γ : Set (Set α)} (h : p.Off (Homotopy.cutPlus (M ／ D) (Homotopy.contractionCut M D Γ))) :
    (p.liftContraction hD).Off (Homotopy.cutPlus M Γ) := by
  intro i hi
  exact h i ((Homotopy.mem_cutPlus_contractionCut_iff hD (p.isHyperplane i).1).mpr hi)

theorem liftContraction_closed (p : TuttePath (M ／ D)) (hD : M.IsFlat D)
    (h : Homotopy.Closed p) : Homotopy.Closed (p.liftContraction hD) :=
  congrArg (fun F => F ∪ D) h

theorem liftContraction_word (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    (p.liftContraction hD).word = p.word.map (fun F => F ∪ D) := by
  simp [word,liftContraction,List.map_ofFn,Function.comp_def]

theorem liftContraction_reverse (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    p.reverse.liftContraction hD = (p.liftContraction hD).reverse := rfl

theorem liftContraction_concat (p q : TuttePath (M ／ D)) (hD : M.IsFlat D)
    (hpq : p.terminus = q.origin) :
    (p.concat q hpq).liftContraction hD =
      (p.liftContraction hD).concat (q.liftContraction hD) (congrArg (fun F => F ∪ D) hpq) := by
  apply ext_vertices (p := (p.concat q hpq).liftContraction hD)
    (q := (p.liftContraction hD).concat (q.liftContraction hD) _) rfl
  intro i
  simp only [liftContraction,concat,Fin.cast,Fin.val_mk]
  split <;> rfl

theorem liftContraction_constant (H : Set α) (hH : IsHyperplane (M ／ D) H) (hD : M.IsFlat D) :
    (constant H hH).liftContraction hD = constant (H ∪ D) (hyperplane_union_of_contract hD hH) := rfl

theorem liftContraction_carrier (p : TuttePath (M ／ D)) (hD : M.IsFlat D) :
    (p.liftContraction hD).carrier = p.carrier ∪ D := by
  ext e
  simp only [carrier,liftContraction,Set.mem_iInter,Set.mem_union]
  constructor
  · intro h
    by_cases heD : e ∈ D
    · exact Or.inr heD
    · exact Or.inl (fun i => (h i).resolve_right heD)
  · rintro (h | h) i
    · exact Or.inl (h i)
    · exact Or.inr h
end TuttePath
end TutteFormalization
