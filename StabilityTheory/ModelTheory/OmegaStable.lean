import Mathlib.Data.Set.Countable
import Mathlib.ModelTheory.Skolem
import StabilityTheory.ModelTheory.BaseTypes

open Set
open Cardinal

namespace FirstOrder

namespace Language

universe u v w w' w''

/-!
# Omega-stability preliminaries

This file currently provides the first `omega`-stability-specific layer for
Phase 3, together with a countable elementary-substructure wrapper.
-/

-- section LowenheimSkolem

-- variable {L : Language.{u, v}} {T : L.Theory}
-- variable {M : Type w} [L.Structure M] [M ⊨ T]

-- /-- A countable parameter set in an infinite model is contained in a countable elementary
-- substructure. -/
-- theorem exists_countable_elementarySubstructure [Infinite M]
--     (hL : L.card ≤ ℵ₀) {A : Set M} (hA : A.Countable) :
--     ∃ S : L.ElementarySubstructure M, A ⊆ S ∧ Countable S := by
--   classical
--   obtain ⟨S, hAS, hS⟩ :=
--     exists_elementarySubstructure_card_eq.{u, v, w, max u v} L A ℵ₀
--       (by simp)
--       (by simpa only [lift_aleph0, ge_iff_le, lift_le_aleph0,
--       le_aleph0_iff_subtype_countable, setOf_mem_eq] using hA)
--       (by simpa using hL)
--       (by simp)
--   simp only [lift_aleph0, lift_eq_aleph0] at hS
--   refine ⟨S, hAS, mk_le_aleph0_iff.mp <| le_of_eq hS⟩

-- end LowenheimSkolem

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory)

/-- Parameter-set-based `omega`-stability: every countable parameter set inside a bundled model
has countably many complete `1`-types over it. This is the primitive repository definition for
the current phase. -/
def IsOmegaStable : Prop :=
  ∀ (M : ModelType.{u, v, w} T) (A : Set M),
    A.Countable →
      Countable (L.CompleteTypeOverSet A (Fin 1))

theorem IsOmegaStable.countable_typeOverSet_of_countable
    (hT : IsOmegaStable.{u, v, w} T) (M : ModelType.{u, v, w} T)
    (hM : Countable M) (A : Set M) :
    Countable (L.CompleteTypeOverSet A (Fin 1)) := by
  refine hT M A (to_countable A)

end Theory

end Language

end FirstOrder
