# StabilityTheory

Lean 4 project for formalizing core parts of classical stability theory, with the
long-term goal of reaching Morley's Categoricity Theorem.

## Current Status

- Core model-theoretic infrastructure is in place: syntax, semantics, partial types,
  complete types, and bridges between them.
- Phase 1 is complete: `CompleteType T α` is available as a Stone space, with
  compactness, Hausdorff separation, and basic topology lemmas in
  `StabilityTheory/ModelTheory/Topology/Types.lean`.
- Phase 2 is in progress: `StabilityTheory/Topology/CantorBendixson.lean` now
  defines `iteratedDerivedSet` together with the zero/successor/limit lemmas,
  antitonicity in the ordinal parameter, monotonicity in the set parameter, and
  closedness under `T1` and closedness hypotheses.
- The remaining near-term topology work is `perfectKernel`, pointwise
  `cbRank`, and the bridge API needed later for Morley rank on type spaces.

## Main Modules

- `StabilityTheory/Topology.lean`
- `StabilityTheory/Topology/CantorBendixson.lean`
- `StabilityTheory/ModelTheory/Syntax.lean`
- `StabilityTheory/ModelTheory/Semantics.lean`
- `StabilityTheory/ModelTheory/PartialTypes.lean`
- `StabilityTheory/ModelTheory/Types.lean`
- `StabilityTheory/ModelTheory/Topology/Types.lean`

## Build

```bash
lake build
```
