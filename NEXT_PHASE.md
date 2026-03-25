# Next Phase TODO

This file tracks the active short-term plan: Phase 2, the Cantor-Bendixson
development.

Current snapshot:
- Tasks 1–3 (iteratedDerivedSet, perfectKernel, pointwise cbRank) are
  implemented in `StabilityTheory/Topology/CantorBendixson.lean`.
- Integration and verification are complete.
- **Priority now shifts to completing the Cantor-Bendixson API** before moving
  on to bridge layers or model-theory integration.

## Phase 2: Cantor-Bendixson Rank

Goal:
- [x] Introduce a general-topology development for transfinite derived sets.
- [x] Keep the core API independent of model theory.
- [ ] **Complete the perfectKernel and CB decomposition API (current priority).**
- [ ] Prepare the topology layer needed later for Morley rank on type spaces.

Why this phase matters:
The Stone-space API is now available. The next missing layer is the topological
machinery for iterated derived sets and Cantor-Bendixson rank, which will later be
specialized to type spaces in the Morley-rank development.

---

## Current Priority: Complete Cantor-Bendixson API

The following items are the most urgent work. They are ordered by dependency so
that earlier items unblock later ones.

### P1. perfectKernel basic API (no extra hypotheses needed)

- [ ] `perfectKernel_subset : perfectKernel s ⊆ s`
      (trivial from `perfectKernel_subset_iteratedDerivedSet` at zero).
- [ ] `isClosed_perfectKernel` (intersection of closed sets; needs `IsClosed s`).
- [ ] `perfectKernel_empty : perfectKernel ∅ = ∅`.
- [ ] `perfectKernel_idem : perfectKernel (perfectKernel s) = perfectKernel s`.

### P2. Extract stabilization lemma and maximality

- [ ] Extract `perfectKernel_eq_iteratedDerivedSet` as a standalone lemma
      (currently buried inside the proof of `perfect_perfectKernel`).
- [ ] Prove `perfectKernel` is the largest perfect subset of `s`:
      any perfect `P ⊆ s` satisfies `P ⊆ perfectKernel s`.

### P3. Set-level CB rank

- [ ] Define `setCBRank (s : Set X) : Ordinal` as the stabilization ordinal.
- [ ] Relate `setCBRank` to pointwise `cbRank`:
      `cbRank x < setCBRank s ↔ x ∉ perfectKernel s` (or similar).
- [ ] `cbRank_lt_ord_succ` (rank is bounded by `(succ #(Set X)).ord`).

### P4. Scattered sets and Cantor-Bendixson decomposition

- [ ] Define `IsScattered` (no nonempty perfect subset) or characterize via
      `perfectKernel_eq_empty_iff`.
- [ ] Prove countability of the scattered part `s \ perfectKernel s` under
      `SecondCountableTopology`, either independently or by connecting to
      Mathlib's `exists_countable_union_perfect_of_isClosed`.
- [ ] Establish that `perfectKernel s` equals the `D` in Mathlib's
      `exists_countable_union_perfect_of_isClosed` (bridge the two approaches).
- [ ] `countable_setOf_cbRank_lt_top` under `SecondCountableTopology`
      (the scattered part is countable).

---

## Completed Tasks (for reference)

### Task 1: Iterated Derived Sets — DONE

- [x] Define `iteratedDerivedSet` with transfinite recursion.
- [x] Simp lemmas for zero, successor, limit.
- [x] Antitonicity in ordinal, monotonicity in set.
- [x] Closedness preservation.
- [x] `gfpApprox` refactor investigated and **rejected** (API regression).

### Task 2: Perfect Kernel — DONE (core only)

- [x] Define `perfectKernel` as intersection of all iterated derived sets.
- [x] `perfectKernel_subset_iteratedDerivedSet`.
- [x] Stabilization lemma `iteratedDerivedSet_stay`.
- [x] `perfect_perfectKernel` for closed sets.

### Task 3: Pointwise Cantor-Bendixson Rank — DONE (core only)

- [x] Define `cbRank : s → WithTop Ordinal`.
- [x] `cbRank_le_iff`, `le_cbRank_iff`, `cbRank_eq_iff`.
- [x] `cbRank_eq_top_iff` (membership in perfect kernel).
- [x] `cbRank_mono`.

---

## Later Tasks (deferred until API is complete)

### Task 5: Proof quality clean-up

- [ ] Replace the `Filter.principal_eq_iff_eq` workaround in
      `iteratedDerivedSet_stay` (line 150) with direct set-equality extraction.
- [ ] Change `stayOn` from `abbrev` to `def` to avoid uncontrolled unfolding.

### Task 6: Bridge Lemmas for Model-Theory Use

- [ ] Identify the smallest API that Morley-rank definitions will need.
- [x] Avoid baking `CompleteType`-specific assumptions into the pure topology file.
- [ ] If a specialized bridge file is needed later, keep it separate from the core
      Cantor-Bendixson file.
- [ ] Add the follow-up bridge layer that applies the pure topology API to
      `typesWith` subsets of type spaces without duplicating model-theoretic lemmas.

### Task 6 follow-up: universe design

The ordinal universe parameter `u` in `perfectKernel.{u}` is independent of
the type universe `v`.  When `u < v` the intersection may not capture full
stabilization.  Key theorems already pin `u = v`; document or constrain the
definitions accordingly.

---

## File Layout

- [x] Target: `StabilityTheory/Topology/CantorBendixson.lean`.
- [x] Umbrella: `StabilityTheory/Topology.lean`.
- [x] Imports: pure topology/ordinal modules only.

## Known Blockers

- [ ] Finish the remaining Phase 0 cleanup item in
      `StabilityTheory/ModelTheory/PartialTypes.lean`.
      Current status: `partialTypeOver_iff_realizedIn_elementaryExtension` is present,
      but the explicit `M ↪ₑ[L] N` formulation from `PLAN.md` still appears to be open.

## Acceptance Criteria

- [x] `iteratedDerivedSet` is defined with usable zero/successor/limit lemmas.
- [x] `perfectKernel` is defined with the main containment/stabilization lemmas.
- [x] `cbRank` is defined with the intended rank and perfect-kernel characterizations.
- [x] The topology development is general enough to reuse outside model theory.
- [x] The new file is integrated into the import tree and the repository builds cleanly.
- [ ] `perfectKernel` has the full maximality/decomposition API (P1–P2).
- [ ] Set-level CB rank is defined and connected to pointwise rank (P3).
- [ ] The Cantor-Bendixson decomposition is proved or connected to Mathlib's version (P4).
- [ ] The bridge API for Morley rank on type spaces is packaged in its own follow-up layer.
