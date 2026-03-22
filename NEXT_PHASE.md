# Next Phase TODO

This file tracks the active short-term plan: Phase 2, the Cantor-Bendixson
development.

Current snapshot:
- Tasks 1–3 are implemented in `StabilityTheory/Topology/CantorBendixson.lean`.
- Integration and verification are complete.
- The remaining open work is listed below: structural refactoring, missing
  theorems and API, and the bridge layer for later Morley-rank use on type
  spaces.

## Phase 2: Cantor-Bendixson Rank

Goal:
- [x] Introduce a general-topology development for transfinite derived sets.
- [x] Keep the core API independent of model theory.
- [ ] Prepare the topology layer needed later for Morley rank on type spaces.

Why this phase matters:
The Stone-space API is now available. The next missing layer is the topological
machinery for iterated derived sets and Cantor-Bendixson rank, which will later be
specialized to type spaces in the Morley-rank development.

## File Layout

- [x] Decide the final file path.
      Chosen target: `StabilityTheory/Topology/CantorBendixson.lean`.
- [x] Decide whether to add a top-level `StabilityTheory/Topology.lean` umbrella file.
      Decision: add `StabilityTheory/Topology.lean`.
- [x] Keep imports minimal and topology-only where possible.
      Initial imports stay in pure topology/ordinal modules only.

## Task 1: Iterated Derived Sets

- [x] Define

```lean
def iteratedDerivedSet (s : Set X) : Ordinal -> Set X
```

- [x] Use the intended transfinite recursion:
      `0`, successor, and limit stages.
- [x] Add the basic simplification lemmas for:
      `iteratedDerivedSet s 0`,
      `iteratedDerivedSet s (succ a)`,
      and the limit case.
- [x] Prove antitonicity in the ordinal parameter.
- [x] Prove monotonicity in the set parameter.
- [x] Record closedness lemmas under appropriate hypotheses.

### Task 1 follow-up: refactor onto `gfpApprox`

`iteratedDerivedSet` duplicates `OrdinalApprox.gfpApprox` from
`Mathlib.SetTheory.Ordinal.FixedPointApproximants`.  The monotone operator
`derivedSet` on the complete lattice `Set X` fits `gfpApprox` exactly
(antitone descent, successor = apply `f`, limit = infimum, stabilization via
cardinality).  Refactoring would eliminate ~130 lines of hand-rolled
recursion and reproved stabilization.

- [ ] Package `derivedSet` as `Set X →o Set X` (via `derivedSet_mono`).
- [ ] Define `iteratedDerivedSet s := gfpApprox derivedSetHom s`.
- [ ] Delete the manual `limitRecOn` definition and the duplicated proofs of
      `_antitone`, `_succ_subset`, and `iteratedDerivedSet_stay`; derive them
      from `gfpApprox_antitone`, `gfpApprox_add_one`, and
      `gfpApprox_ord_mem_fixedPoint`.
- [ ] Verify that existing downstream lemmas (`perfectKernel`, `cbRank`, etc.)
      still build after the refactor.

## Task 2: Perfect Kernel

- [x] Define

```lean
def perfectKernel (s : Set X) : Set X
```

- [x] Prove the kernel is contained in every iterated derived set.
- [x] Prove the main stabilization lemma and use it to identify the kernel with a
      stabilized derived set when needed.
- [x] Prove the downstream perfection statement currently needed:
      `perfect_perfectKernel` for closed sets.

### Task 2 follow-up: missing API and theorems

- [ ] Extract `perfectKernel_eq_iteratedDerivedSet` as a standalone lemma
      (currently buried inside the proof of `perfect_perfectKernel`).
- [ ] Add `perfectKernel_subset : perfectKernel s ⊆ s` (trivial from `_zero`).
- [ ] Add `isClosed_perfectKernel` (intersection of closed sets).
- [ ] Prove `perfectKernel` is the largest perfect subset of `s`:
      any perfect `P ⊆ s` satisfies `P ⊆ perfectKernel s`.
- [ ] Add `perfectKernel_idem : perfectKernel (perfectKernel s) = perfectKernel s`.
- [ ] Add `perfectKernel_empty : perfectKernel ∅ = ∅`.
- [ ] Add `perfectKernel_eq_empty_iff` (scattered-set characterization).

### Task 2 follow-up: Cantor-Bendixson decomposition

- [ ] Prove countability of the scattered part `s \ perfectKernel s` under
      `SecondCountableTopology`, either independently or by connecting to
      Mathlib's `exists_countable_union_perfect_of_isClosed`.
- [ ] Establish that `perfectKernel s` equals the `D` in Mathlib's
      `exists_countable_union_perfect_of_isClosed` (bridge the two approaches).

### Task 2 follow-up: universe design

The ordinal universe parameter `u` in `perfectKernel.{u}` is independent of
the type universe `v`.  When `u < v` the intersection may not capture full
stabilization.  Key theorems already pin `u = v`; document or constrain the
definitions accordingly.

## Task 3: Pointwise Cantor-Bendixson Rank

- [x] Define

```lean
noncomputable def cbRank (s : Set X) (x : s) : WithTop Ordinal
```

- [x] State the membership characterization:
      `cbRank s x = a` means `x` disappears exactly at stage `a + 1`.
- [x] State the `top` case in terms of membership in the perfect kernel.
- [x] Record the current basic API (`≤`, `≥`, `=`, `⊤`, monotonicity) in a form
      usable by later topology/model-theory bridge code.
- [ ] Add `cbRank_lt_ord_succ` (rank is bounded by `(succ #(Set X)).ord`).
- [ ] Add `countable_setOf_cbRank_lt_top` under `SecondCountableTopology`
      (the scattered part is countable).
- [ ] Add any final convenience wrapper if downstream Morley-rank definitions want
      an API that hides the subtype witness.

## Task 4: Proof quality clean-up

- [ ] Replace the `Filter.principal_eq_iff_eq` workaround in
      `iteratedDerivedSet_stay` (line 150) with direct set-equality extraction.
- [ ] Change `stayOn` from `abbrev` to `def` to avoid uncontrolled unfolding.

## Task 5: Bridge Lemmas for Later Model-Theory Use

- [ ] Identify the smallest API that Morley-rank definitions will need.
- [x] Avoid baking `CompleteType`-specific assumptions into the pure topology file.
- [ ] If a specialized bridge file is needed later, keep it separate from the core
      Cantor-Bendixson file.

## Integration

- [x] Add the new file to the project's import tree once the location is fixed.
- [ ] Add the follow-up bridge layer that applies the pure topology API to
      `typesWith` subsets of type spaces without duplicating model-theoretic lemmas.
- [x] Avoid touching existing model-theory files unless a clean import edge requires it.

## Verification

- [x] Check the new file with Lean diagnostics during development.
- [x] Build the file directly once it exists.
- [x] Run `lake build`.
- [x] Confirm the repository still compiles cleanly after the new topology module is
      added.

## Acceptance Criteria

- [x] `iteratedDerivedSet` is defined with usable zero/successor/limit lemmas.
- [x] `perfectKernel` is defined with the main containment/stabilization lemmas.
- [x] `cbRank` is defined with the intended rank and perfect-kernel characterizations.
- [x] The topology development is general enough to reuse outside model theory.
- [x] The new file is integrated into the import tree and the repository builds cleanly.
- [ ] `iteratedDerivedSet` is refactored onto `gfpApprox` (Task 1 follow-up).
- [ ] `perfectKernel` has the full maximality/decomposition API (Task 2 follow-ups).
- [ ] The Cantor-Bendixson decomposition is proved or connected to Mathlib's version.
- [ ] The bridge API for Morley rank on type spaces is packaged in its own follow-up layer.

## Known Blockers

- [ ] Finish the remaining Phase 0 cleanup item in
      `StabilityTheory/ModelTheory/PartialTypes.lean`.
      Current status: `partialTypeOver_iff_realizedIn_elementaryExtension` is present,
      but the explicit `M ↪ₑ[L] N` formulation from `PLAN.md` still appears to be open.
- [x] Decide whether to introduce a top-level topology umbrella module before adding
      more topology files.
