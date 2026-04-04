# Plan

This file tracks the active short-term plan. The current phase is now the
first base-parameter and countable-stability layer after the completion of the
Stone-space and Cantor-Bendixson developments. In the revised roadmap, Morley
rank is postponed until after Morley's Categoricity Theorem, so the immediate
priority is the over-parameters API and the definition of `IsOmegaStable`
needed by the Marker-style route.

Current snapshot:
- Phase 0, Phase 1, and Phase 2 are complete in the current implementation.
- `CompleteType T α` and the current topology layer cover type spaces over a
  theory, not yet type spaces over a base model or parameter set.
- There is not yet any local file for `IsOmegaStable`, isolated types,
  strongly minimal sets, saturated models, or prime models.
- The next step is to build a base-dependent type interface and define
  `IsOmegaStable` independently of Morley rank.

## Phase 3: Parameterized Types and Omega-Stability

Goal:
- [ ] Extend the local API to describe complete types or equivalent
      definitional surrogates over base models or parameter sets.
- [ ] Fix the local representation of the countable type spaces used in the
      definition of `IsOmegaStable`.
- [ ] Define `IsOmegaStable` without going through Morley rank or total
      transcendence.
- [ ] Provide the first transport lemmas needed later for omitting types,
      prime models, and strongly minimal sets.

Why this phase matters:
The revised roadmap follows Marker and Baldwin-Lachlan more closely. Morley
rank is no longer the next target. What is missing now is a base-dependent
type interface and an explicit `omega`-stability definition that later phases
can use directly.

---

## Current Priority: Base-Dependent Type Spaces

The current work should focus on a minimal first layer that exposes types over
bases and makes `omega`-stability a first-class notion in the repository,
without routing the definition through Morley rank.

### P1. Representation Layer

- [ ] Choose the local encoding of "type over a base model or parameter set"
      used by the stability API.
- [ ] Keep the first implementation compatible with later isolated-type,
      prime-model, and strongly minimal developments.
- [ ] Prefer minimal extensions of the existing `PartialType`,
      `PartialTypeOver`, and `CompleteType` APIs rather than introducing a
      broad monster-model abstraction immediately.

### P2. Core Declarations

- [ ] Introduce the first base-dependent complete-type wrapper or equivalent
      declarations.
- [ ] Define `IsOmegaStable` for countable complete theories against that
      interface.
- [ ] Make the countability assumptions explicit in the definition rather than
      hiding them behind later rank-theoretic equivalences.
- [ ] Leave Morley rank, Morley degree, and total transcendence out of the
      initial file.

### P3. Construction Strategy

- [ ] Decide whether the first API is over countable models, countable
      parameter sets, or both, and document that choice in the implementation.
- [ ] Prove the elementary-extension or change-of-base lemmas needed to
      transport the chosen definition.
- [ ] Keep the Stone-space and Cantor-Bendixson layers as comparison tools
      only; they should not dictate the definition of `IsOmegaStable`.
- [ ] Avoid committing early to the final strongly minimal or prime-model
      statements unless the base interface forces them.

### P4. First API Lemmas

- [ ] Invariance under isomorphism or logical equivalence of the chosen base.
- [ ] Monotonicity or transport lemmas under elementary embeddings and
      enlarging the base.
- [ ] Countability-transfer lemmas connecting the chosen base notion to later
      omitting-types statements.
- [ ] Basic lemmas connecting realized types or isolated types to the new
      interface where needed.

### P5. Follow-up Boundary

- [ ] Put the first stability layer in
      `StabilityTheory/ModelTheory/OmegaStable.lean`.
- [ ] Leave isolated types, omitting types, atomic or prime models, and
      strongly minimal sets to later phases unless the representation layer
      forces small supporting declarations earlier.
- [ ] Leave Morley rank, total transcendence, and Cantor-Bendixson comparison
      to the post-categoricity phase.

---

## Existing Implementation Relevant to This Phase

The current phase should respect the following implemented content.

### Model-theory layer

- [x] `PartialType`, `PartialTypeOver`, and realization in elementary
      extensions.
- [x] `CompleteType`, `typeOf`, and the bridge from local partial-type API to
      Mathlib's complete-type API.

### Stone-space layer

- [x] `CompactSpace (T.CompleteType α)`.
- [x] `T2Space (T.CompleteType α)`.
- [x] `CompleteType.isCompact_typesWith`.
- [x] `CompleteType.continuous_typeOf`.
- [x] Closed and clopen wrappers for `typesWith`.

### Cantor-Bendixson layer

- [x] `iteratedDerivedSet`.
- [x] `perfectKernel`.
- [x] `setCBRank`.
- [x] `cbRank`.
- [x] Perfect or scattered decomposition results in the pure-topology file.

---

## Non-goals for This Plan Revision

- [ ] Do not define `IsOmegaStable` via Morley rank or total transcendence.
- [ ] Do not define Morley rank in this phase.
- [ ] Do not force a larger over-parameters interface than the first
      stability file actually needs.
- [ ] Do not treat the Cantor-Bendixson API as the main path to Morley's
      theorem.
- [ ] Do not reopen the completed Phase 0, Phase 1, or Phase 2 work except
      for minimal supporting lemmas.

## Acceptance Criteria

- [ ] `StabilityTheory/ModelTheory/OmegaStable.lean` exists.
- [ ] The repository has an explicit base-dependent interface for the types
      counted in `IsOmegaStable`.
- [ ] `IsOmegaStable` is defined without Morley rank.
- [ ] The first invariance, change-of-base, and countability lemmas are
      proved.
- [ ] The plan stays aligned with the existing `CompleteType` and topology API
      while leaving Morley rank for the later post-categoricity phase.
