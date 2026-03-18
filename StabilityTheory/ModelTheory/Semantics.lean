import Mathlib.ModelTheory.Semantics
import StabilityTheory.ModelTheory.Syntax

namespace FirstOrder

namespace Language

namespace Formula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {α : Type u'}

@[simp]
theorem realize_exClosure [DecidableEq α] (φ : L.Formula α) :
    φ.exClosure.Realize M ↔
      ∃ v : φ.freeVarFinset → M, Formula.Realize (φ.restrictFreeVar id) v := by
  simp [Sentence.Realize, Formula.exClosure, Formula.realize_iExs]

theorem realize_exClosure_of_realize_equivSentence [DecidableEq α] [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] {φ : L.Formula α}
    (h : (Formula.equivSentence φ).Realize M) : φ.exClosure.Realize M := by
  rw [Formula.realize_exClosure]
  exists fun a => (L.con (a : α) : M)
  apply (BoundedFormula.realize_restrictFreeVar'
    (s := (φ.freeVarFinset : Set α)) Set.Subset.rfl
    (v := fun a => (L.con a : M))).2
  exact (φ.realize_equivSentence M).1 h

theorem exists_realize_equivSentence_of_realize_exClosure [DecidableEq α] [Nonempty M]
    {φ : L.Formula α} (h : φ.exClosure.Realize (M := M)) :
    ∃ v : α → M,
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        (Formula.equivSentence φ) := by
  classical
  obtain ⟨v, hv⟩ := (φ.realize_exClosure (M := M)).1 h
  let v' : α → M := fun a =>
    if hmem : a ∈ φ.freeVarFinset then v ⟨a, hmem⟩ else Classical.choice inferInstance
  exists v'
  have hvEq : v' ∘ (↑) = v := by aesop
  have hv' : Formula.Realize (φ.restrictFreeVar id) (v' ∘ (↑)) := by
    simp_all only [realize_exClosure]
  have hφ : φ.Realize v' := by
    apply
      (BoundedFormula.realize_restrictFreeVar' (s := (φ.freeVarFinset : Set α))
        Set.Subset.rfl).1
    simpa [Set.inclusion_eq_id] using hv'
  exact
    (Formula.realize_equivSentence_symm M (Formula.equivSentence φ) v').1 (by simpa)

end Formula

end Language

end FirstOrder
