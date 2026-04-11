import StabilityTheory.ModelTheory.Types

open Set

namespace FirstOrder

namespace Language

universe u v w w' w''

/-!
# Base-dependent type spaces

This file provides the thin base-dependent type-space layer needed for Phase 3.
-/

section Models

variable (L : Language.{u, v})
variable (M : Type w) [L.Structure M] (α : Type w')

/-- Partial types over the base structure `M`, using its full elementary diagram. -/
abbrev PartialTypeOverModel :=
  (L.elementaryDiagram M).PartialType α

/-- Complete types over the base structure `M`, using its full elementary diagram. -/
abbrev CompleteTypeOver :=
  (L.elementaryDiagram M).CompleteType α

variable {M : Type w} [L.Structure M] {α : Type w'}

/-- The complete type of a tuple over the base structure `M`. -/
abbrev typeOfOver {N : Type w'} [L[[M]].Structure N] [Nonempty N]
    [N ⊨ L.elementaryDiagram M] (v : α → N) :
    L.CompleteTypeOver M α :=
  (L.elementaryDiagram M).typeOf v

namespace CompleteTypeOver

/-- Forgetting completeness recovers the underlying partial type over the base structure. -/
abbrev toPartialTypeOverModel (p : L.CompleteTypeOver M α) :
    L.PartialTypeOverModel M α :=
  Theory.CompleteType.toPartialType p

end CompleteTypeOver

end Models

section ParameterSets

variable (L : Language.{u, v})
variable {M : Type w} [L.Structure M]
variable (A : Set M) (α : Type w')

/-- Complete types over a parameter set `A` inside the structure `M`. -/
abbrev CompleteTypeOverSet :=
  (L[[A]].completeTheory M).CompleteType α

variable {A : Set M} {α : Type w'}

/-- The complete type of a tuple over the parameter set `A` inside `M`. -/
abbrev typeOfOverSet {N : (L[[A]].completeTheory M).ModelType} (v : α → N) :
    L.CompleteTypeOverSet A α :=
  (L[[A]].completeTheory M).typeOf v

namespace CompleteTypeOverSet

/-- Forgetting completeness recovers the underlying partial type over `A`. -/
abbrev toPartialTypeOverSet (p : L.CompleteTypeOverSet A α) :
    Theory.PartialTypeOver (L := L) A α :=
  Theory.CompleteType.toPartialType p

/-- A complete type over `A` can be viewed as a partial type over any larger parameter set. -/
abbrev liftParamsToPartial {B : Set M} [Nonempty M] (hAB : A ⊆ B)
    (p : L.CompleteTypeOverSet (M := M) A α) :
    Theory.PartialTypeOver (L := L) B α :=
  Theory.PartialType.liftParams (L := L) (M := M) (A := A) (B := B) hAB
    (Theory.CompleteType.toPartialType p)

end CompleteTypeOverSet

end ParameterSets

end Language

end FirstOrder
