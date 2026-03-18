import Mathlib.ModelTheory.Syntax

namespace FirstOrder

namespace Language

namespace Formula

variable {L : Language.{u, v}} {α : Type u'}

variable [DecidableEq α] in
/-- `exClosure φ` is the sentence asserting that there exist values for all free variables of `φ`
such that `φ` holds. -/
noncomputable def exClosure (φ : L.Formula α) : L.Sentence :=
  iExs φ.freeVarFinset (Formula.relabel Sum.inr (φ.restrictFreeVar id))

end Formula

end Language

end FirstOrder
