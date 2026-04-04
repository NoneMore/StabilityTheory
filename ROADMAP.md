# Roadmap: Formalizing Stability Theory - Road to Morley's Theorem

## Overview

This roadmap extends the existing partial-type and type-space infrastructure
toward the formalization of classical stability theory, with
**Morley's Categoricity Theorem** as the primary milestone.

The current implementation already has a Stone-space topology on
`CompleteType T α` and a general Cantor-Bendixson API. Those developments
remain part of the project, but they are no longer on the critical path to the
categoricity proof. Following Marker, Chapter 6, more closely, the main route
now goes through types over parameters, `omega`-stability, omitting types,
prime and saturated models, indiscernibles, and strongly minimal sets. Standard
Morley rank is postponed until after Morley's theorem and treated as a later
rank-theoretic comparison layer.

## Upstream Interface Status

| Concept | Current Status |
|---|---|
| `CompleteType`, `typeOf`, `realizedTypes` | `Mathlib.ModelTheory.Types` with local wrappers in `StabilityTheory/ModelTheory/Types.lean` |
| Stone topology (`TotallySeparatedSpace`, `isClopen_typesWith`, `IsTopologicalBasis`) | `Mathlib.ModelTheory.Topology.Types` with local extensions in `StabilityTheory/ModelTheory/Topology/Types.lean` |
| `Cardinal.Categorical`, Los-Vaught test | `Mathlib.ModelTheory.Satisfiability` |
| Compactness theorem | `Mathlib.ModelTheory.Satisfiability` |
| Downward Lowenheim-Skolem | `Mathlib.ModelTheory.Skolem` |
| Upward Lowenheim-Skolem | `Mathlib.ModelTheory.Satisfiability` |
| Definable sets (`Definable`, `DefinableSet`) | `Mathlib.ModelTheory.Definability` |
| Elementary embeddings and elementary substructures | `Mathlib.ModelTheory.ElementaryMaps`, `Mathlib.ModelTheory.Substructures` |
| Direct limits | `Mathlib.ModelTheory.DirectLimit` |
| Fraisse limits | `Mathlib.ModelTheory.Fraisse` |
| DLO and `aleph0`-categoricity of DLO | `Mathlib.ModelTheory.Order` |
| `derivedSet`, `Perfect`, `Preperfect`, `AccPt` | `Mathlib.Topology.DerivedSet`, `Mathlib.Topology.Perfect` |
| Alexander's subbasis theorem | `Mathlib.Topology.Compactness.Compact` |
| `PartialType`, `PartialTypeOver`, bridge to `CompleteType` | This project |
| Complete types over parameter models or parameter sets | Not yet exposed in the current local API |
| `omega`-stability, isolated types, strongly minimal sets, prime models | Not yet exposed in the current local API |

## Overall Formalization Strategy

We follow the Baldwin-Lachlan route as presented in Marker, Chapter 6, with
the project's topological development kept available as infrastructure and as a
later comparison tool rather than as the next foundational phase.

1. Build the Stone-space topology on spaces of complete types over theories.
2. Develop Cantor-Bendixson analysis for the relevant topological spaces.
3. Introduce the over-parameters or over-model interfaces needed for the
   countable stability notions used directly in Morley's theorem.
4. Define `omega`-stability independently of Morley rank and build the first
   base-change and countability lemmas around it.
5. Formalize isolated types and the Omitting Types Theorem.
6. Build saturated, atomic, and prime models over the chosen parameter bases.
7. Develop indiscernibles and the Ehrenfeucht-Mostowski theorem.
8. Formalize strongly minimal sets and the dimension theory needed for the
   Baldwin-Lachlan classification argument.
9. Prove Morley's Categoricity Theorem.
10. Return to Morley rank, Morley degree, total transcendence, and the
    comparison with Cantor-Bendixson rank after the categoricity theorem is in
    place.

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
topology and expose the basic API needed later for type-space arguments.

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

**Goal:** develop the topological Cantor-Bendixson machinery for later
comparison theorems and for the topological side of type-space arguments,
without making it a prerequisite for the categoricity proof.

Implemented content:
- [x] Transfinite iterated derived sets.
- [x] Perfect-kernel API.
- [x] Pointwise Cantor-Bendixson rank.
- [x] Set-level stabilization ordinal and related rank bounds.
- [x] Scattered and perfect decomposition API in the pure-topology layer.

Files:
- `StabilityTheory/Topology/CantorBendixson.lean`

## Phase 3: Parameterized Types and Omega-Stability

**Status: PLANNED**

**Goal:** expose the over-parameters interfaces needed for later model-theory
work and define `omega`-stability directly, without routing the definition
through Morley rank.

Tasks:
- [ ] Extend the local API as needed to talk about complete types and definable sets over parameter models or parameter sets.
- [ ] Choose the first working base notion for the repository, and package the corresponding change-of-base lemmas.
- [ ] Define `IsOmegaStable` for countable complete theories against that interface.
- [ ] Prove the first invariance, monotonicity, and countability-transfer lemmas needed later.
- [ ] Keep the countable stability layer independent of total transcendence and Morley rank.

Files:
- `StabilityTheory/ModelTheory/OmegaStable.lean`
- supporting extensions to `StabilityTheory/ModelTheory/Types.lean` and `StabilityTheory/ModelTheory/Topology/Types.lean`

## Phase 4: Isolated Types and Omitting Types

**Status: PLANNED**

**Goal:** formalize isolation and omission in the countable setting needed for
atomic and prime-model constructions.

Tasks:
- [ ] Define isolated or principal types over the chosen base notion from Phase 3.
- [ ] Relate isolated types to the Stone-topological API where that comparison is useful.
- [ ] Formalize the Omitting Types Theorem for countable complete theories.
- [ ] Package the supporting construction lemmas needed later for countable atomic or prime models.

Files:
- `StabilityTheory/ModelTheory/OmittingTypes.lean`
- supporting extensions to `StabilityTheory/ModelTheory/Types.lean` and `StabilityTheory/ModelTheory/Topology/Types.lean`

## Phase 5: Saturated, Atomic, and Prime Models

**Status: PLANNED**

**Goal:** formalize the model-construction layer used in the strongly minimal
analysis and in the final categoricity argument.

Saturated models depend primarily on Phase 3. Atomic and prime-model existence
additionally depends on Phase 4.

Tasks:
- [ ] Define `κ`-saturation.
- [ ] Prove existence of saturated models in the `omega`-stable setting adopted in Phase 3.
- [ ] Prove uniqueness of saturated models at fixed cardinality in the needed setting.
- [ ] Define atomic models and prime models over parameter sets or base models.
- [ ] Prove existence of countable atomic or prime models using Phase 4.
- [ ] Relate atomicity, primeness, and the chosen base notion in the forms needed later.

Files:
- `StabilityTheory/ModelTheory/Saturated.lean`
- `StabilityTheory/ModelTheory/Atomic.lean`

## Phase 6: Indiscernibles and Ehrenfeucht-Mostowski

**Status: PLANNED**

**Goal:** formalize the combinatorial model-theory layer used to derive
`omega`-stability from uncountable categoricity.

Tasks:
- [ ] Define indiscernibility over parameter sets.
- [ ] Formalize Ramsey's theorem (infinite version) or determine an alternative route.
- [ ] Formalize the Ehrenfeucht-Mostowski existence theorem.
- [ ] Formalize the stretching and transfer lemmas needed later in the categoricity proof.

Files:
- `StabilityTheory/ModelTheory/Indiscernibles.lean`
- `StabilityTheory/Combinatorics/Ramsey.lean` if a local combinatorics layer is needed

## Phase 7: Strongly Minimal Sets and Dimension

**Status: PLANNED**

**Goal:** formalize the strongly minimal layer used on the main path to
Morley's theorem and the dimension theory extracted from it.

Tasks:
- [ ] Define strongly minimal formulas or definable sets over parameters.
- [ ] Develop the algebraicity or closure lemmas for strongly minimal sets that are actually needed downstream.
- [ ] Formalize the exchange or pregeometry facts used to talk about bases and dimension.
- [ ] Relate prime models over strongly minimal sets to bases and dimension.
- [ ] Prove the structural classification lemmas that reduce isomorphism questions to the size of bases or dimensions.

Files:
- `StabilityTheory/ModelTheory/StronglyMinimal.lean`
- supporting extensions to `StabilityTheory/ModelTheory/Atomic.lean` and `StabilityTheory/ModelTheory/Types.lean`

## Phase 8: Morley's Categoricity Theorem

**Status: PLANNED**

**Goal:** complete the final categoricity transfer argument without using
Morley rank as a prerequisite.

Tasks:
- [ ] Prove that uncountable categoricity implies `omega`-stability, using Phase 6 and the Phase 3 definition of `IsOmegaStable`.
- [ ] Extract the strongly minimal configuration needed in the final Baldwin-Lachlan argument.
- [ ] Combine the strongly minimal dimension theory with the saturated and prime-model theory developed earlier.
- [ ] Prove categoricity in every uncountable cardinal.
- [ ] Package the final Morley categoricity statement in the project API.

Files:
- `StabilityTheory/ModelTheory/Morley.lean`

## Phase 9: Morley Rank, Total Transcendence, and Cantor-Bendixson Comparison

**Status: PLANNED**

**Goal:** return after Morley's theorem to standard rank theory and to the
comparison results relating the model-theoretic and topological viewpoints.

Tasks:
- [ ] Extend the local API as needed to talk about formulas, definable sets, and complete types over parameter models or parameter sets in the generality needed for rank theory.
- [ ] Define Morley rank by the standard recursive model-theoretic criterion.
- [ ] Define Morley degree in the ordinal-valued rank regime.
- [ ] Define `IsTotallyTranscendental`.
- [ ] Compare strongly minimality with the corresponding rank-one or degree-one characterizations used in textbooks.
- [ ] Prove the comparison between Morley rank and Cantor-Bendixson rank on the relevant type spaces under the final hypotheses adopted in the implementation.
- [ ] Prove the standard countable-theory equivalence between `omega`-stability and total transcendence in the final implementation.

Files:
- `StabilityTheory/ModelTheory/MorleyRank.lean`
- supporting extensions to `StabilityTheory/ModelTheory/OmegaStable.lean` and `StabilityTheory/ModelTheory/Topology/Types.lean`

## Dependency Graph

```text
Phase 0 (Cleanup)
  |
  v
Phase 1 (Stone Space)
  |
  +------------------------------+----------------------+
  v                              v                      v
Phase 2 (CB Analysis)      Phase 3 (Types +         Phase 6
                           omega-stability)         (Indiscernibles/EM)
                                  |                      |
                                  +-----------+----------+
                                  |           |
                                  v           v
                          Phase 4 (Isolated/OT)  Phase 5 (Saturated)
                                  |           \      |
                                  |            \     v
                                  |             +-> Phase 5 contd.
                                  |                 (Atomic/Prime)
                                  |                      |
                                  +----------------------+
                                                         v
                                            Phase 7 (Strongly Minimal)
                                                         |
                                                         v
                                                  Phase 8 (Morley)
                                                         |
                                                         v
                                                  Phase 9 (Morley Rank)
```

Notes on parallelism:
- Phase 2 is no longer on the critical path to Morley's theorem. It now feeds the later Morley-rank comparison phase.
- Phase 6 can begin after Phase 1, although its final theorem statements should target the Phase 3 definition of `IsOmegaStable`.
- Phase 5 splits internally: saturation depends mainly on Phase 3, while atomic or prime-model existence additionally depends on Phase 4.
- Phase 7 depends on the parameterized type infrastructure from Phase 3 and on the model-construction layer from Phase 5.
- Phase 9 is intentionally downstream of Morley's theorem, even though some of its supporting interface work will reuse material from Phases 2 and 3.

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
    OmegaStable.lean
    Saturated.lean
    Atomic.lean
    OmittingTypes.lean
    Indiscernibles.lean
    StronglyMinimal.lean
    Morley.lean
    MorleyRank.lean
  Combinatorics/
    Ramsey.lean
```
