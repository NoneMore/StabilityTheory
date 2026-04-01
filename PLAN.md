# Plan

This file tracks the active short-term plan. The current phase is the first
Morley-rank layer after the completion of the Stone-space and
Cantor-Bendixson developments.

Current snapshot:
- Phase 0, Phase 1, and Phase 2 are complete in the current implementation.
- There is not yet any local file for Morley rank, Morley degree, or
  `IsOmegaStable`.
- The next step is to interpret the existing Cantor-Bendixson API on type
  spaces directly, without introducing a separate bridge-layer milestone.

## Phase 3: Morley Rank and Omega-Stability

Goal:
- [ ] Introduce the first model-theoretic Morley-rank file.
- [ ] Define the core Morley-rank declarations needed downstream.
- [ ] Prove the first formula-level API lemmas from the existing topology layer.
- [ ] Isolate the later `IsOmegaStable` work from the initial rank API.

Why this phase matters:
The repository now has the Stone-space topology on `CompleteType` and a
general Cantor-Bendixson development. The next missing layer is the
model-theoretic interpretation of that topological API for definable subsets
of type spaces.

---

## Current Priority: Morley-Rank Core API

The current work should focus on a minimal first file that turns the existing
topology results into a usable model-theory API.

### P1. File and import setup

- [ ] Create `StabilityTheory/ModelTheory/MorleyRank.lean`.
- [ ] Import `StabilityTheory.ModelTheory.Topology.Types` and
      `StabilityTheory.Topology.CantorBendixson`.
- [ ] Add the new file to `StabilityTheory/ModelTheory.lean` only after the
      initial API is stable.

### P2. Core declarations

Intended declarations for this phase:

```lean
noncomputable def morleyRank (φ : L[[α]].Sentence) : WithTop Ordinal

noncomputable def morleyDegree (φ : L[[α]].Sentence) : ENat

def IsOmegaStable (T : L.Theory) : Prop
```

Phase-3-first-pass scope:
- [ ] Define `morleyRank` in the new file.
- [ ] Defer `morleyDegree` until the rank API is stable enough to state it
      cleanly.
- [ ] Defer `IsOmegaStable` to the follow-up file
      `StabilityTheory/ModelTheory/OmegaStable.lean`.

### P3. Rank construction strategy

- [ ] Use the existing pure-topology API directly on `typesWith (T := T) φ`.
- [ ] Avoid a standalone bridge file unless repeated proof patterns make one
      unavoidable.
- [ ] Introduce only local helper lemmas or abbreviations when they remove
      persistent subtype-witness noise in `MorleyRank.lean`.
- [ ] Choose the final `morleyRank` definition so that the `top` case matches
      the persistence of a perfect kernel, rather than hiding that case in an
      always-ordinal set-level definition.

### P4. First API lemmas

The first batch of theorems should be stated as explicit declarations in the
new file, with final names determined by the implementation.

- [ ] Invariance under formula equivalence.
- [ ] Monotonicity under inclusion of `typesWith` sets, hence under implication.
- [ ] The relation between ordinal-valued rank and the absence of the perfect
      kernel.
- [ ] Any zero-rank or inconsistent-formula characterization that falls out
      cleanly from the chosen definition.

### P5. Follow-up boundary with Omega-stability

- [ ] Decide which results belong in `MorleyRank.lean` and which should be
      deferred to `OmegaStable.lean`.
- [ ] Leave the main equivalence
      `IsOmegaStable ↔ all formula ranks are ordinal-valued`
      to the follow-up phase, unless the chosen rank definition forces part of
      that statement to be proved earlier.

---

## Existing Implementation Relevant to This Phase

The current phase should build directly on the following implemented content.

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
- [x] Perfect/scattered decomposition results in the pure-topology file.

---

## Non-goals for This Plan Revision

- [ ] Do not add a dedicated `ModelTheory/Topology/CantorBendixson.lean`
      bridge layer as a planning milestone.
- [ ] Do not redesign later roadmap phases from the current implementation.
- [ ] Do not reopen the completed Phase 0 cleanup inside the Morley-rank file.

## Acceptance Criteria

- [ ] `StabilityTheory/ModelTheory/MorleyRank.lean` exists.
- [ ] `morleyRank` is defined against the current type-space API.
- [ ] The first formula-level monotonicity and equivalence lemmas are proved.
- [ ] The chosen definition exposes the `top` case in a way compatible with the
      later `omega`-stability equivalence.
- [ ] The plan stays aligned with the implemented topology API and does not
      depend on a separate bridge-layer file.
