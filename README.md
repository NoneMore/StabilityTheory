# StabilityTheory

Lean 4 project for formalizing core parts of classical stability theory, with the
long-term goal of reaching Morley's Categoricity Theorem.

## Current Status

- Core model-theoretic infrastructure is in place: syntax, semantics, partial types,
  complete types, and bridges between them.
- Phase 1 is complete: `CompleteType T α` is available as a Stone space, with
  compactness, Hausdorff separation, and basic topology lemmas in
  `StabilityTheory/ModelTheory/Topology/Types.lean`.
- The next mathematical milestone is Cantor-Bendixson rank, followed by Morley rank
  and ω-stability.

## Main Modules

- `StabilityTheory/ModelTheory/Syntax.lean`
- `StabilityTheory/ModelTheory/Semantics.lean`
- `StabilityTheory/ModelTheory/PartialTypes.lean`
- `StabilityTheory/ModelTheory/Types.lean`
- `StabilityTheory/ModelTheory/Topology/Types.lean`

## Build

```bash
lake build
```

## Planning Docs

- `PLAN.md`: full roadmap from the current infrastructure to Morley's theorem.
- `NEXT_PHASE.md`: short-term working note for the next active phase after the
  completed Stone-space milestone.
