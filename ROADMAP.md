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

### Mathlib availability survey (as of 2026-04)

| Concept | Status |
|---|---|
| Infinite Ramsey theorem (monochromatic subset for `f : [ω]^n → Fin k`) | **Not in Mathlib.** Finite Ramsey is also absent. Hales-Jewett and Hindman are present (`Mathlib.Combinatorics.HalesJewett`, `Mathlib.Combinatorics.Hindman`) but are not substitutes. |
| Cardinal pigeonhole (`Ordinal.infinite_pigeonhole`) | `Mathlib.SetTheory.Cardinal.Pigeonhole` — available, formulated via cofinality. |
| Finite pigeonhole / `Finite.exists_infinite_fiber` | `Mathlib.Data.Fintype.Pigeonhole` — available. |
| Indiscernible sequences or sets | **Not in Mathlib.** No `Indiscernible` definition exists in `Mathlib.ModelTheory`. |
| Ehrenfeucht-Mostowski functor | **Not in Mathlib.** |
| Skolem functions / Skolemization | `Mathlib.ModelTheory.Skolem` provides downward Löwenheim-Skolem but not explicit Skolem-function terms. |
| Well-ordered linear extensions of arbitrary cardinality | `Ordinal`, `Cardinal`, and `LinearOrder` on `Ordinal` are available. `Cardinal.ord` gives a well-order of any cardinal. |
| Direct limits of structures | `Mathlib.ModelTheory.DirectLimit` — available. |

### Mathematical outline

The role of this phase in the categoricity proof is the contrapositive
direction: if a countable complete theory `T` is `κ`-categorical for some
uncountable `κ`, then `T` is `omega`-stable. The argument runs:

1. Assume `T` is not `omega`-stable: there exists a countable model `M`
   with uncountably many complete `1`-types over it.
2. Extract a binary tree of formulas witnessing `2^{aleph_0}` many types.
3. Use Ramsey's theorem (infinite version for pairs, `n = 2`, `k = 2`) to
   extract an indiscernible sequence of order type `omega` inside a model
   of `T`.
4. Apply the Ehrenfeucht-Mostowski theorem to stretch that indiscernible
   sequence to an indiscernible sequence of any given order type `I`,
   producing a model `EM(T, I)`.
5. Show that different order types of the same cardinality can yield
   non-isomorphic models, contradicting `κ`-categoricity.

### Sub-phase 6a: Infinite Ramsey theorem

Since Mathlib has neither finite nor infinite Ramsey, we must provide a
self-contained proof of the infinite version for pairs. The statement
needed is:

> For any coloring `f : [ω]^2 → Fin k`, there exists an infinite
> monochromatic subset.

The standard proof goes by iterated application of
`Finite.exists_infinite_fiber` (available in Mathlib) over a decreasing
sequence of infinite sets.

Tasks:
- [ ] Define `n`-element subsets `[S]^n` for a set `S` (or for a type),
      at least for `n = 2`. Decide between `Finset`-based or
      `Fin n → S`-based encoding; the latter is more compatible with
      the model-theoretic notion of `n`-tuples.
- [ ] State the infinite Ramsey theorem for pairs with finitely many
      colors: for `f : (Fin 2 ↪o α) → Fin k` and `α` infinite, there
      exists an infinite subset on which `f` is constant.
- [ ] Prove the theorem by iterating `Finite.exists_infinite_fiber`.
      The standard proof constructs a sequence `a₀, a₁, …` with each
      `aₙ` chosen from a progressively refined infinite subset; by
      pigeonhole on the `k` colors, one color class is hit infinitely
      often.
- [ ] (Optional) Generalize to `n`-tuples if the EM construction in
      Phase 6c requires `n > 2`. For the standard Morley proof only
      `n = 2` is needed, but the general version is a modest
      extension.

Design note: The coloring should be stated for order-preserving
injections `Fin 2 ↪o α` rather than unordered pairs, because the
model-theoretic notion of indiscernibility is order-sensitive.

Files:
- `StabilityTheory/Combinatorics/Ramsey.lean`

### Sub-phase 6b: Indiscernible sequences

Tasks:
- [ ] Define `IsIndiscernible`: a sequence `f : I → M` indexed by a
      linear order `I` is indiscernible over a parameter set `A` if for
      every `n`, every two order-preserving injections
      `σ₁ σ₂ : Fin n ↪o I`, and every `L[[A]]`-formula `φ` in `n`
      variables, `M ⊨ φ(f ∘ σ₁) ↔ M ⊨ φ(f ∘ σ₂)`.
- [ ] Define `IsIndiscernibleSet`: the same but for all injections, not
      just order-preserving ones. This is the stronger notion used in
      some presentations but not required for the main Morley argument.
- [ ] Prove basic closure properties: indiscernibility is preserved
      under elementary embeddings, restriction to sub-orders, and
      reindexing by order isomorphisms.
- [ ] Prove that an indiscernible sequence over `A` has a well-defined
      EM-type: the `n`-type of any `n`-element increasing subsequence is
      the same.
- [ ] (Extraction) Apply Ramsey (Sub-phase 6a) to extract an
      indiscernible sequence of order type `ω` from any infinite
      sequence in a model of `T`, possibly after passing to an
      elementary extension. This is the key combinatorial step. The
      argument: given a sequence `(aᵢ)_{i < ω}`, color each pair
      `{i, j}` by the quantifier-free type of `(aᵢ, aⱼ)`; by Ramsey,
      extract a monochromatic subsequence; by compactness, extend to a
      full indiscernible sequence in an elementary extension.
- [ ] Package the compactness argument cleanly: the set of sentences
      asserting indiscernibility of a sequence of new constants is
      finitely satisfiable (using the Ramsey subsequence), hence
      satisfiable.

Design notes:
- The definition should use `Fin n ↪o I` for compatibility with the
  Ramsey output and with Mathlib's `BoundedFormula.realize`.
- The parameter set `A` should use the Phase 3 convention
  (`Set M` or bundled model).
- The file should not depend on Phase 4 or Phase 5.

Files:
- `StabilityTheory/ModelTheory/Indiscernibles.lean`

### Sub-phase 6c: Ehrenfeucht-Mostowski theorem

The EM theorem says: given a complete Skolemized theory `T` and an
indiscernible sequence of order type `ω`, there is a canonical way to
build a model `EM(T, I)` for any infinite linear order `I`, containing
an indiscernible sequence indexed by `I`.

Tasks:
- [ ] Formalize the Skolemization step. Mathlib's `Mathlib.ModelTheory.Skolem`
      provides downward Löwenheim-Skolem via Skolem functions, but does
      not expose Skolem-function terms in the language. The options are:
      (a) Expand `L` by Skolem-function symbols and work in `L^S`,
      proving that any `L`-theory has a conservative Skolem expansion.
      (b) Avoid explicit Skolem functions by working with the Skolem-hull
      construction already available in Mathlib (the closure of a set
      under definable functions). Option (b) is more Mathlib-compatible
      but requires careful handling.
      **Decision required at implementation time.**
- [ ] Define the EM functor `EM(T, I)`: given an EM-type `Φ` (the
      common `n`-type of increasing `n`-tuples) and a linear order `I`,
      construct the term model generated by `I` modulo the theory `T`
      expanded by the EM-type. This is a quotient of the Skolem-term
      algebra.
- [ ] Prove that `EM(T, I)` is a model of `T` and contains an
      indiscernible sequence indexed by `I`.
- [ ] Prove the cardinality bound: `#EM(T, I) = max(#I, #L, ℵ₀)`.
- [ ] Prove the stretching lemma: for any two infinite linear orders
      `I` and `J`, `EM(T, I)` and `EM(T, J)` realize the same
      `L`-sentences (they are elementarily equivalent).

Design notes:
- The construction uses `Mathlib.ModelTheory.DirectLimit` or a term-model
  quotient. The term algebra can be built as
  `FreeStructure L (Σ n, (Fin n → I))` or similar; the details depend
  on whether we choose explicit Skolem functions.
- Universe care: `I` lives in a potentially different universe from `M`.
  The EM model should live in `max u v w` where `w` is the universe of
  `I`.
- The Skolemization choice (option a vs b above) is the main engineering
  decision for this sub-phase and should be resolved before coding
  begins.

Files:
- `StabilityTheory/ModelTheory/EhrenfeuchtMostowski.lean`
- `StabilityTheory/ModelTheory/Skolemization.lean` (if option (a) is chosen)

### Sub-phase 6d: Uncountable categoricity implies omega-stability

This sub-phase combines 6a–6c to prove the implication needed in Phase 8.

Tasks:
- [ ] State and prove: if `T` is a countable complete theory that is
      `κ`-categorical for some uncountable `κ`, then `T` is
      `omega`-stable (in the sense of the Phase 3 definition
      `Theory.IsOmegaStable`).
- [ ] The proof outline:
      1. Assume `T` is not `omega`-stable.
      2. Find a countable `M ⊨ T` with uncountably many `1`-types.
      3. Build a binary tree of consistent formulas splitting types.
      4. Embed `ω` into a model and apply Ramsey extraction (6b) to get
         an indiscernible sequence.
      5. Use EM stretching (6c) to build models of cardinality `κ` with
         different "numbers of independent indiscernibles", yielding
         non-isomorphic models of the same cardinality.
- [ ] Verify that the cardinal arithmetic used (e.g.,
      `2^{aleph_0} > aleph_0`, properties of `κ`) is available in
      Mathlib's `SetTheory.Cardinal`.

Design note: The tree of formulas in step 3 is a standard construction
but is non-trivial to formalize. Consider whether to represent it as a
function `Bool^{<ω} → L.Formula (Fin 1)` or via an inductive type.

Files:
- `StabilityTheory/ModelTheory/Indiscernibles.lean` (or a new file
  `StabilityTheory/ModelTheory/OmegaStableOfCategorical.lean` to
  separate the implication from the definitions)

### Phase 6 dependency summary

```text
Sub-phase 6a (Ramsey)
  |
  v
Sub-phase 6b (Indiscernible sequences)  <-- Phase 3 (for parameter convention)
  |
  v
Sub-phase 6c (EM theorem)  <-- Mathlib.ModelTheory.Skolem, DirectLimit
  |
  v
Sub-phase 6d (categoricity → ω-stability)  <-- Phase 3 (IsOmegaStable)
```

### Estimated scope and risk

| Sub-phase | Estimated effort | Risk |
|---|---|---|
| 6a (Ramsey) | Low-medium. The proof is elementary; the main work is choosing the right encoding of `n`-element subsets. | Low. |
| 6b (Indiscernibles) | Medium. The definition is straightforward; the Ramsey extraction + compactness argument requires care. | Medium — the compactness step involves building a theory in an expanded language with new constants. |
| 6c (EM theorem) | **High.** This is the most complex construction in the entire roadmap. Building a term model in Lean, taking its quotient, and verifying the model axioms is labor-intensive. | **High** — the Skolemization design choice affects the entire sub-phase, and universe management for the term algebra is non-trivial. |
| 6d (categoricity → ω-stability) | Medium. The proof is conceptually clear but involves combining several pieces. | Medium — depends on 6a–6c being clean. |

## Phase 7: Strongly Minimal Sets and Dimension

**Status: PLANNED**

**Goal:** formalize the strongly minimal layer used on the main path to
Morley's theorem and the dimension theory extracted from it.

### Mathlib availability survey (as of 2026-04)

| Concept | Status |
|---|---|
| `Matroid` with `closure`, `IsBase`, `Indep`, rank | `Mathlib.Combinatorics.Matroid.*` — comprehensive API including `closure_exchange`, cardinal rank, circuits. |
| `ClosureOperator` | `Mathlib.Order.Closure` — available as an order-theoretic structure on a `Preorder`. |
| Pregeometry / exchange property (model-theoretic) | **Not in Mathlib.** No `Pregeometry` class exists. However, `Matroid.closure_exchange` provides exactly the exchange axiom for matroid closure. |
| Strongly minimal sets | **Not in Mathlib.** No `StronglyMinimal` definition exists. |
| Model-theoretic algebraic closure (`acl`) | **Not in Mathlib** (field-theoretic `algebraicClosure` is unrelated). |
| Definable sets / `DefinableSet` | `Mathlib.ModelTheory.Definability` — `Definable` predicate and `DefinableSet` bundled type are available. |

### Mathematical outline

In the Baldwin-Lachlan proof of Morley's theorem, the strongly minimal
layer provides the geometric backbone: inside any uncountably categorical
theory, one can find a strongly minimal definable set whose
pregeometry-dimension controls the isomorphism type of the model.

Key mathematical facts needed:

1. **Strongly minimal definition:** A definable set `D` (possibly with
   parameters) is strongly minimal if every definable subset of `D` is
   finite or cofinite (in every elementary extension).
2. **Model-theoretic algebraic closure:** `acl(A)` is the set of
   elements that lie in a finite `A`-definable set.
3. **Exchange property for `acl` in strongly minimal sets:** If `D` is
   strongly minimal, then `acl` restricted to `D` satisfies the
   exchange property: if `b ∈ acl(A ∪ {c}) \ acl(A)` then
   `c ∈ acl(A ∪ {b})`.
4. **Pregeometry and dimension:** The exchange property makes
   `(D, acl)` a pregeometry; quotienting by `acl(∅)` gives a geometry.
   Bases exist and all have the same cardinality (= dimension).
5. **Dimension determines isomorphism:** Two models of an
   `omega`-stable theory that agree on the dimension of the strongly
   minimal set are isomorphic (over the prime model).

### Sub-phase 7a: Model-theoretic algebraic closure

Tasks:
- [ ] Define `acl L A` (algebraic closure of a parameter set `A` in
      a structure `M`): the set of elements `b ∈ M` such that there
      exists an `L[[A]]`-formula `φ(x)` with `M ⊨ φ(b)` and the
      solution set `{c ∈ M | M ⊨ φ(c)}` is finite.
- [ ] Prove `acl` is a closure operator: `A ⊆ acl(A)`, monotonicity
      (`A ⊆ B → acl(A) ⊆ acl(B)`), idempotence (`acl(acl(A)) = acl(A)`).
- [ ] Prove `acl` is preserved under elementary embeddings:
      if `f : M ↪ₑ[L] N` then `f '' acl_M(A) = acl_N(f '' A)`.
- [ ] Prove finite character: `b ∈ acl(A)` iff `b ∈ acl(A₀)` for some
      finite `A₀ ⊆ A`.
- [ ] (Optional) Define `dcl L A` (definable closure): the set of
      elements uniquely defined by an `L[[A]]`-formula. Prove
      `dcl(A) ⊆ acl(A)`. This is not strictly needed for Morley but
      is standard and cheap once `acl` exists.

Design notes:
- The definition of `acl` should reuse `Mathlib.ModelTheory.Definability`
  (`Set.Definable`) for the "definable set" part and require finiteness
  of the solution set.
- The parameter convention should match Phase 3 (`Set M` or bundled
  model).
- Idempotence of `acl` uses compactness (a standard argument); this is
  the most non-trivial lemma here.

Files:
- `StabilityTheory/ModelTheory/AlgebraicClosure.lean`

### Sub-phase 7b: Strongly minimal sets

Tasks:
- [ ] Define `IsStronglyMinimal`: a definable set `D` in `M` (with
      parameters from `A`) is strongly minimal if, in every elementary
      extension `N` of `M`, every `L[[A]]`-definable subset of `D(N)` is
      finite or cofinite in `D(N)`.
- [ ] Prove equivalent formulations:
      (a) `D` is strongly minimal iff the induced theory on `D` is
          strongly minimal (every model has the finite/cofinite
          property).
      (b) `D` is strongly minimal iff every complete `1`-type over any
          parameter set containing `A` either contains `φ_D` or contains
          `¬φ_D`, and the type containing `φ_D` is isolated or
          non-forking in an appropriate sense.
- [ ] Prove that strongly minimal sets are infinite (in any model).
- [ ] Prove that `omega`-stable theories contain strongly minimal
      definable sets. (This uses the type-counting definition from
      Phase 3.)

Design notes:
- The "in every elementary extension" quantifier is the key subtlety.
  In Lean, this means quantifying over all `N : T.ModelType` with an
  elementary embedding `M ↪ₑ[L] N`, or equivalently, working inside a
  monster model convention. The former is more explicit and avoids
  introducing a global monster; the latter is more ergonomic for longer
  proofs. **Decision required at implementation time**, but given the
  project's existing style (no monster model), the explicit formulation
  is recommended.
- The formula `φ_D` defining `D` should be bundled with `D` in a
  structure or passed as an explicit parameter.

Files:
- `StabilityTheory/ModelTheory/StronglyMinimal.lean`

### Sub-phase 7c: Exchange property and pregeometry

This is the mathematical heart of Phase 7: proving that `acl` on a
strongly minimal set satisfies the exchange property, and extracting the
pregeometry/dimension theory from it.

Tasks:
- [ ] Define `Pregeometry` as a structure: a type `α` equipped with a
      closure operator `cl : Set α → Set α` satisfying:
      (i) `A ⊆ cl(A)` (extension),
      (ii) `cl(cl(A)) = cl(A)` (idempotence),
      (iii) finite character (`a ∈ cl(A)` iff `a ∈ cl(A₀)` for some
            finite `A₀ ⊆ A`),
      (iv) exchange (`a ∈ cl(A ∪ {b}) \ cl(A) → b ∈ cl(A ∪ {a})`).
      Alternatively, build `Pregeometry` as a `Matroid` with the
      finitary condition, reusing Mathlib's matroid API directly.
- [ ] **Key design decision: Matroid bridge vs standalone Pregeometry.**
      Option (A): Define `Pregeometry` standalone and prove the exchange
      property directly from the strongly minimal hypothesis. Then
      separately build an instance `Matroid` from any `Pregeometry` to
      import the dimension theory.
      Option (B): Skip `Pregeometry` entirely and directly construct a
      `Matroid` on the strongly minimal set, using
      `Matroid.IndepMatroid.ofFinitary` or `Matroid.ofBase`, with
      `acl`-independence as the independence predicate.
      **Recommendation: Option (A).** A standalone `Pregeometry` is a
      thin layer, is standard in model theory textbooks, and keeps the
      model-theoretic reasoning self-contained. The matroid bridge can
      then be added for dimension results.
- [ ] Prove the exchange property for `acl` on strongly minimal `D`:
      if `b ∈ acl(A ∪ {c}) \ acl(A)` with `b, c ∈ D`, then
      `c ∈ acl(A ∪ {b})`.
      Proof sketch: Since `b ∈ acl(A ∪ {c})`, there is a formula
      `φ(x, c)` with finitely many solutions including `b`. Since `D`
      is strongly minimal, the formula `∃x. φ(x, y)` either has finitely
      many or cofinitely many solutions for `y ∈ D`. If cofinitely many,
      then `c ∈ acl(A ∪ {b})` by symmetry of the finite/cofinite
      dichotomy. The details require careful use of the strongly minimal
      hypothesis in elementary extensions.
- [ ] Construct the `Pregeometry` instance on `(D, acl_D)` where
      `acl_D(A) = acl(A) ∩ D`.

Files:
- `StabilityTheory/ModelTheory/Pregeometry.lean`
- supporting extensions to `StabilityTheory/ModelTheory/AlgebraicClosure.lean`

### Sub-phase 7d: Dimension theory

Tasks:
- [ ] Define `independent` sets and `basis` for a pregeometry (or
      import them from the matroid bridge).
- [ ] Prove that all bases of a pregeometry have the same cardinality.
      **If using the matroid bridge:** this follows from
      `Matroid.InvariantCardinalRank` for finitary matroids, which is
      already in Mathlib (`invariantCardinalRank_of_finitary`).
      **If standalone:** prove directly by the standard
      exchange-based replacement argument.
- [ ] Define `dim D A` as the cardinality of any basis of `D` over
      `acl(A) ∩ D`.
- [ ] Prove dimension is well-defined and invariant under elementary
      equivalence.
- [ ] Prove the dimension formula for strongly minimal sets in models
      of `T`: if `M₁, M₂ ⊨ T` and `dim D(M₁) = dim D(M₂)`, then
      the prime-model extensions are isomorphic.

Design notes:
- The matroid bridge to Mathlib is the most efficient path to the
  equicardinality of bases, since `Matroid.Rank.Cardinal` already
  provides exactly what is needed for finitary matroids. The bridge
  construction:
  1. Given a `Pregeometry (D, cl)`, define independence as
     `Indep I ↔ ∀ a ∈ I, a ∉ cl(I \ {a})`.
  2. Construct `Matroid.ofBase` or `Matroid.IndepMatroid.ofFinitary`
     using the exchange property proved in 7c.
  3. Import `Matroid.cRk`, `Matroid.IsBase.cardinalMk_eq`, etc.
- The dimension-determines-isomorphism theorem (the last task) is the
  centerpiece connecting Phase 7 to Phase 8. Its proof uses the prime
  model theory from Phase 5 and the back-and-forth argument over the
  pregeometry basis.

Files:
- `StabilityTheory/ModelTheory/Pregeometry.lean` (continued)
- `StabilityTheory/ModelTheory/StronglyMinimal.lean` (dimension-isomorphism theorem)

### Sub-phase 7e: Existence of strongly minimal sets in omega-stable theories

Tasks:
- [ ] Prove that any `omega`-stable theory `T` (countable, complete)
      has a strongly minimal definable set (possibly with parameters).
      Proof sketch: by the type-counting definition, there is a formula
      that "maximally splits" types; iterating, one reaches a formula
      whose solution set is strongly minimal.
- [ ] Alternatively, if the Phase 8 proof route derives strong
      minimality from `omega`-stability via the Baldwin-Lachlan
      analysis more directly, this sub-phase can be merged into Phase 8.

Files:
- `StabilityTheory/ModelTheory/StronglyMinimal.lean`

### Phase 7 dependency summary

```text
Sub-phase 7a (acl)  <-- Phase 3 (parameter convention), Mathlib.ModelTheory.Definability
  |
  v
Sub-phase 7b (strongly minimal)  <-- Phase 3 (IsOmegaStable), 7a
  |
  v
Sub-phase 7c (exchange + pregeometry)  <-- 7a, 7b
  |
  v
Sub-phase 7d (dimension)  <-- 7c, Mathlib.Combinatorics.Matroid (optional bridge)
  |                            Phase 5 (prime models, for dim-determines-iso)
  v
Sub-phase 7e (existence in ω-stable theories)  <-- 7b, Phase 3
```

### Estimated scope and risk

| Sub-phase | Estimated effort | Risk |
|---|---|---|
| 7a (acl) | Medium. The definition is standard; idempotence requires a compactness argument. | Low-medium. |
| 7b (strongly minimal) | Medium. The definition is clear; the quantification over elementary extensions needs careful universe handling. | Medium — the "every elementary extension" quantifier is the main design challenge. |
| 7c (exchange + pregeometry) | **High.** The exchange property proof is the most technically involved model-theoretic argument in this phase. | **High** — the proof uses the strongly minimal dichotomy in a non-trivial way, manipulating definable sets and their cardinalities across elementary extensions. |
| 7d (dimension) | Medium if using matroid bridge; high if standalone. | Low if matroid bridge works cleanly; medium otherwise. |
| 7e (existence) | Medium. | Low — this is a standard consequence of ω-stability. |

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
Phase 2 (CB Analysis)      Phase 3 (Types +         Phase 6a (Ramsey)
                           omega-stability)              |
                                  |                      v
                                  |                  Phase 6b
                                  |                  (Indiscernibles)
                                  |                      |
                                  +-----------+----------+
                                  |           |          |
                                  v           v          v
                          Phase 4 (Isolated/OT)    Phase 6c (EM theorem)
                                  |       Phase 5       |
                                  |      (Saturated)    |
                                  |           |         |
                                  v           v         v
                              Phase 5 contd.      Phase 6d
                              (Atomic/Prime)   (cat → ω-stable)
                                  |
                     +------------+
                     v
                Phase 7a (acl)
                     |
                     v
                Phase 7b (strongly minimal)
                     |
                     v
                Phase 7c (exchange + pregeometry)
                     |
                     v
                Phase 7d (dimension)  <-- Phase 5 (prime models)
                     |
                     v
              Phase 8 (Morley)  <-- Phase 6d
                     |
                     v
              Phase 9 (Morley Rank)
```

Notes on parallelism:
- Phase 2 is no longer on the critical path to Morley's theorem. It now feeds the later Morley-rank comparison phase.
- Phase 6a (Ramsey) is a pure combinatorics task and can begin immediately after Phase 1, in parallel with Phase 3.
- Phase 6b (Indiscernibles) depends on Phase 3 for the parameter convention, but can begin as soon as Phase 3's core declarations stabilize.
- Phase 6c (EM theorem) is the heaviest single construction in the roadmap. It depends on 6b and on a Skolemization decision. It can proceed in parallel with Phases 4 and 5.
- Phase 6d (categoricity → ω-stability) depends on 6a–6c and Phase 3. It feeds into Phase 8 but not into Phase 7.
- Phase 5 splits internally: saturation depends mainly on Phase 3, while atomic or prime-model existence additionally depends on Phase 4.
- Phase 7 is now split into five sub-phases (7a–7e). Sub-phases 7a–7c form the sequential core; 7d can partially overlap with 7c once the pregeometry is defined; 7e can begin as soon as 7b is done.
- Phase 7d (dimension) benefits from the matroid bridge to Mathlib's `Matroid.Rank.Cardinal`, which provides equicardinality of bases for finitary matroids out of the box.
- Phase 8 depends on both Phase 6d and Phase 7d. These two dependency chains can be developed in parallel.
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
    AlgebraicClosure.lean
    Pregeometry.lean
    StronglyMinimal.lean
    Saturated.lean
    Atomic.lean
    OmittingTypes.lean
    Indiscernibles.lean
    Skolemization.lean          (if explicit Skolem-function approach is chosen)
    EhrenfeuchtMostowski.lean
    Morley.lean
    MorleyRank.lean
  Combinatorics/
    Ramsey.lean
```
