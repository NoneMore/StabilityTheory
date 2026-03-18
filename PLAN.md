# Plan: Partial Types With Parameters in `Mathlib.ModelTheory`

## Overview

Add model-theoretic partial types to Mathlib: satisfiable sets of formulas
over a first-order theory, with parameter support via `withConstants`.

Design principles:

- Primary representation is a set of `L.Formula alpha`, not a closed theory.
- Parameters handled through `L[[A]]` and `completeTheory`, matching
  `CompleteType`, `Definable`, and `elementaryDiagram`.
- `CompleteType` is not refactored; new API bridges to it.

## Current State

### Phase 1: core file — COMPLETE

`Mathlib/ModelTheory/PartialTypes.lean` compiles cleanly. Contents:

- `Theory.withSet`, `Theory.PartialType`, `SetLike` / `PartialOrder`,
  `ofSet`, `toTheory`, `isSatisfiable`, `subset_toTheory`,
  `mem_toTheory_of_mem`.
- `reductModelType`, `isRealizedIn_reductModelType` (constructive bridge
  from models of `p.toTheory` to realizers).
- `RealizedBy`, `IsRealizedIn`, `exists_modelType_isRealizedIn`.
- Compactness characterizations: `partialType_iff_finitelyRealizable`,
  `partialType_completeTheory_iff_finitelyRealizable`,
  `partialTypeOver_iff_finitelyRealizable`.
- `PartialTypeOver` (abbrev over `completeTheory`).
- Parameter transport: `mapSet`, `partialType_completeTheory_map`,
  `liftSet`, `partialTypeOver_mono`, `liftParams`.
- `partialTypeOver_iff_realizedIn_elementaryExtension` (Phase 3 intermediate).

### Phase 2: CompleteType bridge — NOT STARTED

### Phase 3: elementary embedding formulation — INTERMEDIATE ONLY

Has the iff with `ModelType (L.elementaryDiagram M)` but not the final
statement with `↪ₑ`.

---

## Phase 2: Bridge To `CompleteType`

**This is the immediate priority.** It resolves the TODO in both
`Types.lean` and `PartialTypes.lean`.

All additions go in `Mathlib/ModelTheory/Types.lean` (which will import
`PartialTypes.lean`). No changes to `PartialTypes.lean`.

### `CompleteType.toPartialType`

```lean
def CompleteType.toPartialType (p : T.CompleteType alpha) : T.PartialType alpha
```

Underlying set: `{phi | Formula.equivSentence phi ∈ (p : L[[alpha]].Theory)}`.
Satisfiability: the induced `withSet` theory is a subtheory of `p`, which is
satisfiable by `p.isMaximal.1`.

### Membership bridge

```lean
theorem CompleteType.mem_toPartialType
    (p : T.CompleteType alpha) {phi : L.Formula alpha} :
    phi ∈ p.toPartialType ↔ Formula.equivSentence phi ∈ p
```

Definitional; this mediates between `SetLike` for `L.Formula alpha`
(on `PartialType`) and `SetLike` for `L[[alpha]].Sentence` (on `CompleteType`).

### Subset helper

```lean
theorem CompleteType.toPartialType_toTheory_subset
    (p : T.CompleteType alpha) :
    p.toPartialType.toTheory ⊆ (p : L[[alpha]].Theory)
```

Follows from `p.subset'` (for the `onTheory T` part) and `mem_toPartialType`
(for the `equivSentence` image part).

### Extension to complete type

```lean
theorem PartialType.exists_modelType_realized_completeType
    (p : T.PartialType alpha) :
    ∃ M : Theory.ModelType T, ∃ q ∈ T.realizedTypes M alpha,
      (p : Set (L.Formula alpha)) ⊆ q.toPartialType
```

Proof:

1. `p.exists_modelType_isRealizedIn` gives `M` and `v : alpha → M` with
   `p.RealizedBy v`.
2. Let `q := T.typeOf v`. Then `q ∈ T.realizedTypes M alpha` by definition.
3. For `phi ∈ p`: `phi.Realize v` (from `RealizedBy`), so
   `Formula.equivSentence phi ∈ T.typeOf v` (by `formula_mem_typeOf`), so
   `phi ∈ q.toPartialType` (by `mem_toPartialType`).

Derive the simpler form by forgetting the model:

```lean
theorem PartialType.exists_le_completeType (p : T.PartialType alpha) :
    ∃ q : T.CompleteType alpha, (p : Set (L.Formula alpha)) ⊆ q.toPartialType
```

### Compatibility with `typeOf`

```lean
theorem CompleteType.realizedBy_typeOf (v : alpha → M) :
    (T.typeOf v).toPartialType.RealizedBy v
```

Direct from `mem_toPartialType` and `formula_mem_typeOf`.

---

## Phase 3: Elementary Extension Realization

Not blocking the first merge.

### Current intermediate result

`partialTypeOver_iff_realizedIn_elementaryExtension` gives an iff between
consistency of a parameterized formula set and realizability in some
`N : ModelType (L.elementaryDiagram M)`, with formulas transported along
`(↑) : A → M` via `lhomWithConstantsMap`.

### Target

```lean
theorem PartialTypeOver.exists_elementaryExtension_realizing
    {A : Set M} (p : PartialTypeOver (L := L) A alpha) :
    ∃ N : Bundled L.Structure, ∃ e : M ↪ₑ[L] N, ∃ v : alpha → N,
      ∀ phi ∈ p,
        ((L.lhomWithConstantsMap (fun a : A => e a)).onFormula phi).Realize v
```

### Route

1. Forward direction of the intermediate iff gives
   `N : ModelType (L.elementaryDiagram M)` and `v`.
2. `ElementaryEmbedding.ofModelsElementaryDiagram` extracts `e : M ↪ₑ[L] N`.
3. Verify the composition `A → M → N` via `e` matches the
   `lhomWithConstantsMap ((↑) : A → M)` reduct on `N`.

---

## Risks

1. **Circular imports**: `PartialTypes.lean` must not import `Types.lean`.
   Bridge goes in `Types.lean`.
2. **Membership semantics**: `PartialType` is `SetLike` for `L.Formula alpha`;
   `CompleteType` is `SetLike` for `L[[alpha]].Sentence`.
   `mem_toPartialType` bridges them via `equivSentence`.
3. **Universes**: existence theorems produce models in
   `Type (max u v w)`. Keep annotations explicit.
4. **Scope creep**: Phase 3 is optional. First PR = Phase 1 + Phase 2.

## Out Of Scope

Topology, isolation, saturation, omitting types, `RealizedBy ↔ Model`
iff, refactoring `CompleteType` in terms of `PartialType`.

## Verification

1. `lake env lean Mathlib/ModelTheory/PartialTypes.lean`
2. `lake env lean Mathlib/ModelTheory/Types.lean`
3. No existing `CompleteType` declaration names change.
4. `lake build` before PR.

## TODO List

- [x] Finish Phase 1 in `Mathlib/ModelTheory/PartialTypes.lean`.
- [ ] Add `CompleteType.toPartialType` in `Mathlib/ModelTheory/Types.lean`.
- [ ] Prove `CompleteType.mem_toPartialType`.
- [ ] Prove `CompleteType.toPartialType.toTheory ⊆ (p : L[[alpha]].Theory)`.
- [ ] Prove `PartialType.exists_modelType_realized_completeType`.
- [ ] Derive `PartialType.exists_le_completeType`.
- [ ] Prove `CompleteType.realizedBy_typeOf`.
- [ ] Keep the bridge in `Types.lean` only; do not introduce a circular import with `PartialTypes.lean`.
- [ ] Preserve existing `CompleteType` declaration names.
- [ ] If time permits, finish the Phase 3 theorem using `M ↪ₑ[L] N`.
- [ ] Verify with `lake env lean Mathlib/ModelTheory/PartialTypes.lean`.
- [ ] Verify with `lake env lean Mathlib/ModelTheory/Types.lean`.
- [ ] Run `lake build` before opening a PR.
