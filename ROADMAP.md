# Roadmap: Formalizing Stability Theory — Road to Morley's Theorem

## Overview

This roadmap extends the existing partial-type and type-space infrastructure
toward the formalization of classical stability theory, with
**Morley's Categoricity Theorem** as the primary milestone.

## Upstream Interface Status

| Concept | Mathlib Location |
|---|---|
| `CompleteType`, `typeOf`, `realizedTypes` | `Mathlib.ModelTheory.Types` |
| Stone topology (`TotallySeparatedSpace`, `isClopen_typesWith`, `IsTopologicalBasis`) | `Mathlib.ModelTheory.Topology.Types` |
| `Cardinal.Categorical`, Łoś–Vaught test | `Mathlib.ModelTheory.Satisfiability` |
| Compactness theorem | `Mathlib.ModelTheory.Satisfiability` |
| Downward Löwenheim–Skolem | `Mathlib.ModelTheory.Skolem` |
| Upward Löwenheim–Skolem | `Mathlib.ModelTheory.Satisfiability` |
| Definable sets (`Definable`, `DefinableSet`) | `Mathlib.ModelTheory.Definability` |
| Elementary embeddings and elementary substructures | `Mathlib.ModelTheory.ElementaryMaps`, `Mathlib.ModelTheory.Substructures` |
| Direct limits | `Mathlib.ModelTheory.DirectLimit` |
| Fraisse limits | `Mathlib.ModelTheory.Fraisse` |
| DLO and `aleph0`-categoricity of DLO | `Mathlib.ModelTheory.Order` |
| `derivedSet`, `Perfect`, `Preperfect`, `AccPt` | `Mathlib.Topology.DerivedSet`, `Mathlib.Topology.Perfect` |
| Alexander's subbasis theorem | `Mathlib.Topology.Compactness.Compact` |
| `PartialType`, `PartialTypeOver`, bridge to `CompleteType` | This project |

## Overall Formalization Strategy

We follow the Baldwin-Lachlan route as presented in standard sources such as
Marker, Chapter 6, and Tent-Ziegler, Chapter 5.

1. Build the Stone-space topology on spaces of complete types.
2. Develop Cantor-Bendixson analysis for the relevant topological spaces.
3. Define Morley rank, Morley degree, and `omega`-stability.
4. Build saturated, atomic, and prime models.
5. Prove the Omitting Types Theorem.
6. Develop indiscernibles and the Ehrenfeucht-Mostowski theorem.
7. Prove Morley's Categoricity Theorem.

The current-phase plan with finer-grained task tracking lives in `PLAN.md`.

## Phase 0: Cleanup of Previous Plan

**Status: COMPLETE**

**Goal:** complete the cleanup around realization in elementary
extensions.

Tasks:
- [x] Add `partialTypeOver_iff_realizedIn_elementaryExtension`.
- [x] State the elementary-extension realization theorem with an explicit `M ↪ₑ[L] N` formulation.
- [x] Keep the existing partial-type files building cleanly.

Files:
- `StabilityTheory/ModelTheory/PartialTypes.lean`

## Phase 1: Stone Space of Complete Types

**Status: COMPLETE**

**Goal:** establish that `CompleteType T α` carries the expected Stone-space
topology and expose the basic API needed later for rank arguments.

Implemented content:
- [x] `CompactSpace (CompleteType T α)`.
- [x] `T2Space (CompleteType T α)`.
- [x] Compactness lemmas for basic opens such as `CompleteType.isCompact_typesWith`.
- [x] Continuity of the `typeOf` map via `CompleteType.continuous_typeOf`.
- [x] Closed and clopen wrappers for basic definable subsets.
- [x] Integration into the repository import tree.

Files:
- `StabilityTheory/ModelTheory/Topology/Types.lean`

## Phase 2: Cantor-Bendixson Analysis

**Status: COMPLETE**

**Goal:** develop the topological Cantor-Bendixson machinery needed later for
Morley rank, while keeping the core API independent of model theory.

Implemented content:
- [x] Transfinite iterated derived sets.
- [x] Perfect-kernel API.
- [x] Pointwise Cantor-Bendixson rank.
- [x] Set-level stabilization ordinal and related rank bounds.
- [x] Scattered and perfect decomposition API in the pure-topology layer.

Files:
- `StabilityTheory/Topology/CantorBendixson.lean`

## Phase 3: Morley Rank and Omega-Stability

**Status: PLANNED**

**Goal:** define Morley rank from the Cantor-Bendixson analysis of type spaces,
introduce Morley degree, and formalize `omega`-stability in a form usable by the
later model-construction phases.

Tasks:
- [ ] Define Morley rank for formulas or definable sets through the type-space topology.
- [ ] Define Morley degree in the ordinal-valued rank regime.
- [ ] Define `IsOmegaStable`.
- [ ] Prove the main equivalence: `IsOmegaStable T ↔ ∀ φ, morleyRank φ < ⊤`.
- [ ] Establish the basic monotonicity and finite-union behavior needed downstream.

Files:
- `StabilityTheory/ModelTheory/MorleyRank.lean`
- `StabilityTheory/ModelTheory/OmegaStable.lean`

## Phase 4: Saturated and Atomic Models

**Status: PLANNED**

**Goal:** formalize the model-construction layer used in the classical
categoricity argument.

Saturated models depend on Phase 3 only. Atomic and prime models additionally
depend on Phase 5 (Omitting Types Theorem) for the existence construction.

Tasks:
- [ ] Define `κ`-saturation.
- [ ] Prove existence of saturated models in the `omega`-stable setting.
- [ ] Prove uniqueness of saturated models at fixed cardinality.
- [ ] Define atomic models and prime models.
- [ ] Prove existence of countable atomic models via the Omitting Types Theorem (Phase 5).
- [ ] Relate atomicity and primeness and formalize the main uniqueness results over parameters.

Files:
- `StabilityTheory/ModelTheory/Saturated.lean`
- `StabilityTheory/ModelTheory/Atomic.lean`

## Phase 5: Omitting Types Theorem

**Status: PLANNED**

**Goal:** formalize the omission of non-isolated types in countable models.

Tasks:
- [ ] Fix the final theorem statement against the current type-space API.
- [ ] Formalize the omission theorem for countable complete theories.
- [ ] Package the supporting construction lemmas needed later in the categoricity argument.

Files:
- `StabilityTheory/ModelTheory/OmittingTypes.lean`

## Phase 6: Indiscernibles and Ehrenfeucht-Mostowski

**Status: PLANNED**

**Goal:** formalize the combinatorial model-theory layer used to derive
`omega`-stability from uncountable categoricity.

Tasks:
- [ ] Define indiscernibility over parameter sets.
- [ ] Formalize Ramsey's theorem (infinite version) or determine an alternative route.
      Mathlib does not currently provide the needed Ramsey-theoretic interface;
      a local `Combinatorics/Ramsey.lean` file will likely be required.
- [ ] Formalize the Ehrenfeucht-Mostowski existence theorem.
- [ ] Formalize the stretching and transfer lemmas needed for later applications.

Files:
- `StabilityTheory/ModelTheory/Indiscernibles.lean`
- `StabilityTheory/Combinatorics/Ramsey.lean` if a local combinatorics layer is needed

## Phase 7: Morley's Categoricity Theorem

**Status: PLANNED**

**Goal:** complete the final categoricity transfer argument.

Tasks:
- [ ] Prove that uncountable categoricity implies `omega`-stability.
- [ ] Combine `omega`-stability with the saturated and prime-model theory developed earlier.
- [ ] Prove categoricity in every uncountable cardinal.
- [ ] Package the final Morley categoricity statement in the project API.

Files:
- `StabilityTheory/ModelTheory/Morley.lean`

## Dependency Graph

```text
Phase 0 (Cleanup)
  |
  v
Phase 1 (Stone Space)
  |
  +---------------------------+
  v                           v
Phase 2 (CB Analysis)    Phase 6 (Indiscernibles/EM)
  |                           |
  v                           |
Phase 3 (Morley Rank)         |
  |                           |
  +-------------+             |
  v             v             |
Phase 5 (OT)  Phase 4        |
  |           (Saturated)     |
  +------+------+             |
         v                    |
   Phase 4 contd.             |
   (Atomic/Prime)             |
         |                    |
         +----------+---------+
                    v
             Phase 7 (Morley)
```

Notes on parallelism:
- Phase 6 can proceed independently of Phases 2–5 after Phase 1.
- Phase 4 (saturated models) and Phase 5 (Omitting Types) can proceed in
  parallel after Phase 3.
- Phase 4 (atomic/prime models) requires Phase 5 for the existence
  construction.

## Suggested File Structure

```text
StabilityTheory/
  Topology.lean
  Topology/
    CantorBendixson.lean
  ModelTheory/
    Syntax.lean
    Semantics.lean
    PartialTypes.lean
    Types.lean
    Topology/
      Types.lean
    MorleyRank.lean
    OmegaStable.lean
    Saturated.lean
    Atomic.lean
    OmittingTypes.lean
    Indiscernibles.lean
    Morley.lean
  Combinatorics/
    Ramsey.lean
```
