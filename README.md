# StabilityTheory

Lean 4 project for formalizing core parts of classical stability theory. The
primary theorem milestone is Morley's Categoricity Theorem, and the long-term
goal is a reusable Lean library for the topological and model-theoretic
infrastructure that theorem depends on.

## Project Goals

- Formalize the basic type-space and rank-theoretic machinery used in the
  classical route to Morley's Categoricity Theorem, including Morley rank,
  omega-stability, saturated and prime-model constructions, and the final
  categoricity theorem.
- Develop, in the longer term, a reusable Lean library that could support
  stability-theoretic work beyond the current roadmap, with possible targets
  including the Ryll-Nardzewski theorem, definability of types in stable
  theories, and parts of forking or independence calculus.

## Current Status

Major results and significant changes are listed here in reverse chronological
order.

- 2026-03-30: Cantor-Bendixson analysis is formalized.
- 2026-03-25: `PartialType` and its interface with `CompleteType` are in place.

## Project Structure

- `README.md`: top-level project overview, milestones, structure, references,
  and limitations.
- `ROADMAP.md`: project-wide roadmap and long-range design document.
- `PLAN.md`: current-phase planning document and short-term task tracker.
- `StabilityTheory/ModelTheory/*.lean`: syntax, semantics, `PartialType`, and
  `CompleteType`.
- `StabilityTheory/ModelTheory/Topology/*.lean`: topology on type spaces.
- `StabilityTheory/Topology/*.lean`: pure-topology development, currently
  centered on Cantor-Bendixson analysis.

## Correspondence with Non-formal Materials

- The overall route follows the Baldwin-Lachlan style development summarized in
  Marker, Chapter 6, and Tent-Ziegler, Chapter 5.
- Reference texts usually phrase the topology of type spaces as `S_n(T)` and
  related Stone spaces. This project uses Mathlib's `CompleteType` and
  `typesWith` APIs instead, so some important definitions are packaged
  differently from the textbook presentation.
- The Cantor-Bendixson development is first formalized as a pure-topology API
  and only then specialized to type spaces. In non-formal sources, the same
  ideas are often introduced directly inside the Morley-rank development.
- The `PartialType` to `CompleteType` transition is made explicit through
  project-specific bridge definitions and lemmas. Reference materials typically
  treat this passage more implicitly.

## Current Limitations

- Morley rank, Morley degree, omega-stability, saturated models, atomic and
  prime models, the Omitting Types Theorem, indiscernibles, the
  Ehrenfeucht-Mostowski theorem, and Morley's Categoricity Theorem are not yet
  formalized in this repository.
- There is not yet a `StabilityTheory/ModelTheory/MorleyRank.lean` or
  `StabilityTheory/ModelTheory/OmegaStable.lean` file.
- The current status section intentionally tracks only the two most developed
  implemented areas; it is not a complete changelog for the repository.
