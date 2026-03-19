# Next Phase TODO

This file tracks the active short-term plan: Phase 2, the Cantor-Bendixson
development.

## Phase 2: Cantor-Bendixson Rank

Goal:
- [ ] Introduce a general-topology development for transfinite derived sets.
- [ ] Keep the core API independent of model theory.
- [ ] Prepare the topology layer needed later for Morley rank on type spaces.

Why this phase matters:
The Stone-space API is now available. The next missing layer is the topological
machinery for iterated derived sets and Cantor-Bendixson rank, which will later be
specialized to type spaces in the Morley-rank development.

## File Layout

- [ ] Decide the final file path.
      Preferred target: `StabilityTheory/Topology/CantorBendixson.lean`.
- [ ] Decide whether to add a top-level `StabilityTheory/Topology.lean` umbrella file.
- [ ] Keep imports minimal and topology-only where possible.

## Task 1: Iterated Derived Sets

- [ ] Define

```lean
def iteratedDerivedSet (s : Set X) : Ordinal -> Set X
```

- [ ] Use the intended transfinite recursion:
      `0`, successor, and limit stages.
- [ ] Add the basic simplification lemmas for:
      `iteratedDerivedSet s 0`,
      `iteratedDerivedSet s (succ a)`,
      and the limit case.
- [ ] Prove antitonicity in the ordinal parameter.
- [ ] Prove monotonicity in the set parameter.
- [ ] Record closedness lemmas under appropriate hypotheses.

## Task 2: Perfect Kernel

- [ ] Define

```lean
def perfectKernel (s : Set X) : Set X
```

- [ ] Prove the kernel is contained in every iterated derived set.
- [ ] Prove the stabilization/intersection lemmas needed later.
- [ ] Under compact `T1` hypotheses, prove the kernel is perfect or isolate the exact
      lemma statement needed downstream.

## Task 3: Pointwise Cantor-Bendixson Rank

- [ ] Define

```lean
noncomputable def cbRank (s : Set X) (x : X) : WithTop Ordinal
```

- [ ] State the membership characterization:
      `cbRank s x = a` means `x` disappears exactly at stage `a + 1`.
- [ ] State the `top` case in terms of membership in the perfect kernel.
- [ ] Prefer statements that are usable later for `typesWith` subsets of type spaces.

## Task 4: Bridge Lemmas for Later Model-Theory Use

- [ ] Identify the smallest API that Morley-rank definitions will need.
- [ ] Avoid baking `CompleteType`-specific assumptions into the pure topology file.
- [ ] If a specialized bridge file is needed later, keep it separate from the core
      Cantor-Bendixson file.

## Integration

- [ ] Add the new file to the project's import tree once the location is fixed.
- [ ] Reuse the Stone-space API from `StabilityTheory.ModelTheory.Topology.Types`
      without duplicating model-theoretic lemmas here.
- [ ] Avoid touching existing model-theory files unless a clean import edge requires it.

## Verification

- [ ] Check the new file with Lean diagnostics during development.
- [ ] Build the file directly once it exists.
- [ ] Run `lake build`.
- [ ] Confirm the repository still compiles cleanly after the new topology module is
      added.

## Acceptance Criteria

- [ ] `iteratedDerivedSet` is defined with usable zero/successor/limit lemmas.
- [ ] `perfectKernel` is defined with the main containment/intersection lemmas.
- [ ] `cbRank` is defined with the intended rank and perfect-kernel characterizations.
- [ ] The topology development is general enough to reuse outside model theory.
- [ ] The new file is integrated into the import tree and the repository builds cleanly.

## Known Blockers

- [ ] Finish the remaining Phase 0 cleanup item in
      `StabilityTheory/ModelTheory/PartialTypes.lean`.
- [ ] Decide whether to introduce a top-level topology umbrella module before adding
      more topology files.
