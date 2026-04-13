import Mathlib.ModelTheory.Satisfiability

/-!
# Supplemental satisfiability API

This file collects generic satisfiability lemmas that extend
`Mathlib/ModelTheory/Satisfiability`. It is intentionally separate so the
contents can be backported upstream cleanly.
-/

namespace FirstOrder

namespace Language

namespace Theory

universe u v

variable {L : Language.{u, v}} {T : L.Theory}

namespace IsSatisfiable

/-- A satisfiable theory cannot contain both a sentence and its negation. -/
theorem false_of_mem_of_not_mem (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ ∈ T)
    (hφnot : φ.not ∈ T) : False := by
  obtain ⟨M⟩ := hT
  exact (M.is_model.realize_of_mem _ hφnot) (M.is_model.realize_of_mem _ hφ)

end IsSatisfiable

end Theory

end Language

end FirstOrder
