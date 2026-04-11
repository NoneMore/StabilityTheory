# Plan

This file tracks the active short-term plan.  The current phase remains the
omega-stability interface layer.  The over-model and over-parameter-set type
spaces (`CompleteTypeOver`, `CompleteTypeOverSet`) compile, and the primitive
definition of `IsOmegaStable` has now been switched back to the parameter-set
formulation.  The remaining work is the comparison with over-model type spaces
and the first restriction and transport lemmas.

Current snapshot:
- Phase 0, Phase 1, and Phase 2 are complete.
- `BaseTypes.lean` already provides `CompleteTypeOver`,
  `CompleteTypeOverSet`, `typeOfOver`, `typeOfOverSet`, and
  `liftParamsToPartial`.
- `OmegaStable.lean` already uses the parameter-set-based definition of
  `Theory.IsOmegaStable` and proves the first countability corollary over
  subsets of countable models.
- `LanguageMapOnUniv.lean` now packages the low-level comparison between
  `L[[M]]` and `L[[Set.univ : Set M]]`, including
  `withConstantsMapToUniv`, `withConstantsMapFromUniv`,
  `withConstantsEquivUniv`, the two `IsExpansionOn` instances on `M`, and the
  sentence-, theory-, and complete-theory transport lemmas attached to this
  canonical equivalence.
- The intended counted type spaces for `omega`-stability are complete `1`-types
  `L.CompleteTypeOverSet A (Fin 1)` over countable parameter sets `A`.
- Over-model type spaces `L.CompleteTypeOver M (Fin 1)` remain part of the
  local interface, but they should be treated as a derived companion
  formulation rather than the primitive definition.
- No local file yet for isolated types, strongly minimal sets, saturated
  models, or prime models.
- The low-level full-parameter-set language-map comparison is now in place.
  `CompleteTypeMapOnUniv.lean` now also contains the added-constants base
  theory transport lemmas needed for the next comparison step.  The remaining
  Phase 3 work starts with the induced equivalence on complete types, then
  moves to restriction maps and the first elementary-substructure transport
  lemmas.

## Phase 3: Parameterized Types and Omega-Stability

Goal:
- [x] Introduce the first explicit local API for complete types over bundled
      base models and over parameter sets inside those models.
- [x] Fix the counted type spaces in the first implementation to be complete
      `1`-types, with `Fin 1` as the arity convention.
- [x] Redefine `IsOmegaStable` by countability of complete `1`-types over
      countable parameter sets, without going through Morley rank or total
      transcendence.
- [ ] Recover the countable bundled-model formulation as a derived theorem
      from the parameter-set definition and the full-parameter comparison map.
- [ ] Provide the first transport lemmas needed later for omitting types,
      prime models, and strongly minimal sets.

Why this phase matters:
The revised roadmap follows Marker and Baldwin-Lachlan more closely. Morley
rank is no longer the next target. What is missing now is a base-dependent
type interface and an explicit `omega`-stability definition that later phases
can use directly. The main design choice for this phase is now fixed: the
primitive repository definition should quantify over countable parameter sets
`A : Set M` inside models of `T`. The over-model formulation should survive
as an interface theorem, not as the definition itself, since the two
formulations only agree under additional hypotheses such as the usual
countable-language and complete-theory setting.

---

## Current Priority: Comparison and Transport Lemmas

The over-model and over-parameter-set type spaces are in place, the primitive
`IsOmegaStable` definition has been revised, and the low-level `Set.univ`
language comparison is now packaged.  The next bottleneck is therefore the
complete-type comparison layer itself: identify the bundled-model type space
with the full-parameter-set type space using the existing semantic transport,
then recover the bundled-model countability corollary before moving on to
restriction and elementary-substructure transport.

### Target Definition

    Theory.IsOmegaStable T
      := ∀ (M : T.ModelType) (A : Set M),
           A.Countable → Countable (L.CompleteTypeOverSet (M := M) A (Fin 1))

This keeps the primitive notion meaningful for arbitrary languages and
theories. In particular, no countability assumption on `L` and no
completeness assumption on `T` is built into the definition.

### L1. Redefinition and Immediate Consequences

Status: implemented in `OmegaStable.lean`.

File: `OmegaStable.lean`.  Builds on: `Types.lean` bridge.

**L1.1 — Replace the primitive definition.**

    def Theory.IsOmegaStable : Prop :=
      ∀ (M : T.ModelType) (A : Set M),
        A.Countable → Countable (L.CompleteTypeOverSet (M := M) A (Fin 1))

This should be the only primitive `omega`-stability definition used by the
repository going forward.

**L1.2 — Countability over subsets of countable models.**

    theorem Theory.IsOmegaStable.countable_typeOverSet_of_countable
        (hT : T.IsOmegaStable) (M : T.ModelType) (hM : Countable M)
        (A : Set M) :
        Countable (L.CompleteTypeOverSet (M := M) A (Fin 1))

Immediate from the new definition plus the fact that every subset of a
countable type is countable.

### L2. Full-Parameter-Set Comparison

Builds on: L1.

Status: L2.1 is implemented in `LanguageMapOnUniv.lean`.  The added-constants
base-theory transport lemmas used by L2.2 are now implemented in
`CompleteTypeMapOnUniv.lean`, while the complete-type equivalence and the
bundled-model countability corollary still remain.

The over-model space `L.CompleteTypeOver M (Fin 1)` should remain available,
but only as a derived reformulation of types over the full parameter set of
`M`.

Packaging note:
- The low-level with-constants equivalence and its canonical semantic
  compatibility should live below the complete-type API.
- The induced equivalence on complete types should live in the base-change
  layer built on top of that low-level interface.
- The countability corollary for `IsOmegaStable` should remain in
  `OmegaStable.lean`.

**L2.1 — Compare constants for `M` with constants for `Set.univ : Set M`.**

Status: implemented in `LanguageMapOnUniv.lean`.

Package the obvious bijection between `M` and `Set.univ : Set M` into the
corresponding language equivalence between `L[[M]]` and `L[[Set.univ]]`.
This layer should not stop at a bare `LEquiv`: in the canonical expansions on
the ambient structure `M`, it should also package the induced semantic
compatibility.

Expected deliverables:

    def withConstantsEquivUniv :
        L[[M]] ≃ᴸ L[[Set.univ : Set M]]

using `Equiv.Set.univ M` and the associated `lhomWithConstantsMap` maps.

- Record that both directions of this equivalence are expansions on `M` for
  the canonical interpretations of the new constants.
- Record sentence- and theory-level transport lemmas on `M`, so that later
  layers can rewrite realizability and complete theories without reopening the
  low-level proof.
- Keep the distinction clear between the syntactic object `LEquiv` itself and
  the additional semantic lemmas attached to this particular canonical
  expansion.

Proof strategy:
- Use `Equiv.Set.univ M` (or its symmetric form) to identify the two constant
  index types.
- Build the forward and inverse language maps with `L.lhomWithConstantsMap`.
- Prove the inverse laws by `LHom.funext` and computation on the sum-language
  constructors.
- Prove the semantic compatibility on `M` from
  `Language.constantsOnMap_isExpansionOn`, then derive the sentence and theory
  transport lemmas from `LHom.realize_onSentence` and `LHom.onTheory_model`.

Implemented content:
- `LanguageMapOnUniv.lean` defines `withConstantsMapToUniv`,
  `withConstantsMapFromUniv`, and `withConstantsEquivUniv`.
- It proves the two composition identities for those maps, the two
  `IsExpansionOn` instances on `M`, the sentence- and theory-level transport
  lemmas, and the two complete-theory transport lemmas.

**L2.2 — Transport complete types across that language equivalence.**

    def CompleteTypeOver.equivOverSetUniv (M : T.ModelType) :
        L.CompleteTypeOver M (Fin 1) ≃
          L.CompleteTypeOverSet (M := M) (Set.univ : Set M) (Fin 1)

This is the comparison map that replaces the old use of the bundled-model
definition as primitive.

Implementation note:
- Build this on top of the sentence/theory transport packaged in L2.1, not by
  repeating the raw language-equivalence argument inside the complete-type
  proof.
- The relevant complete theories should be identified via the canonical
  semantic transport on `M`, and the equivalence on complete types should then
  be induced by pushing forward and pulling back maximal theories along the
  `LEquiv.onSentence` bijection.

Current status:
- `CompleteTypeMapOnUniv.lean` now packages the added-constants elementary
  diagram transport lemmas in both directions, so the base-theory alignment
  needed by `toOverSetUniv` and `toOverModelUniv` is available.
- The remaining work in L2.2 is to discharge the `subset'` fields of those
  maps and the inverse-law proofs for `equivOverSetUniv`.

**L2.3 — Recover countability over countable bundled models.**

    theorem Theory.IsOmegaStable.countable_typeOver_of_countable
        (hT : T.IsOmegaStable) (M : T.ModelType) (hM : Countable M) :
        Countable (L.CompleteTypeOver M (Fin 1))

Apply the definition at `A = Set.univ`, then transport along L2.2.

### L3. Restriction Maps and Monotonicity

File: `OmegaStable.lean`.  Builds on: `PartialTypes.lean` compactness, L1, L2.

With the parameter-set formulation primitive, the first change-of-base map
should be restriction along inclusion of parameter sets.

**L3.1 — Restriction of complete types along parameter inclusion.**

    def CompleteTypeOverSet.restrict {A B : Set M} (hAB : A ⊆ B) :
        L.CompleteTypeOverSet (M := M) B (Fin 1) →
          L.CompleteTypeOverSet (M := M) A (Fin 1)

Pull back along the map `L.lhomWithConstantsMap` induced by the inclusion
`A ↪ B`.

**L3.2 — Surjectivity of restriction.**

    theorem CompleteTypeOverSet.restrict_surjective {A B : Set M} (hAB : A ⊆ B) :
        Function.Surjective (CompleteTypeOverSet.restrict (M := M) hAB)

Embed a `CompleteTypeOverSet A` into a partial type over `B`, prove
consistency with `L[[B]].completeTheory M`, extend via
`PartialType.exists_le_completeType`, and verify that restriction returns the
original type.

**L3.3 — Derived over-model restriction.**

    def CompleteTypeOver.restrictToSet (A : Set M) :
        L.CompleteTypeOver M (Fin 1) →
          L.CompleteTypeOverSet (M := M) A (Fin 1)

Define this as the composite of L2.2 with restriction from `Set.univ` to `A`.
This keeps the existing over-model API available without using it as the
primitive notion of `omega`-stability.

### L4. Elementary-Substructure Transport

File: `OmegaStable.lean`.  Builds on: `PartialTypes.lean`
(`partialTypeOver_iff_finitelyRealizable`), L3, and
`Mathlib.ModelTheory.Skolem`.

These lemmas are no longer needed to justify the parameter-set formulation,
but they remain useful later for moving countable parameter sets into smaller
ambient models and for the prime/saturated-model phases.

**L4.1 — Countable elementary submodel containing a set.**

    theorem exists_countable_elementarySubstructure
        [M ⊨ T] (A : Set M) (hA : A.Countable) (hL : L.card ≤ ℵ₀)
        (hM : Infinite M) :
        ∃ S : L.ElementarySubstructure M, A ⊆ S ∧ Countable S

This is still the right Löwenheim–Skolem wrapper for later phases.

**L4.2 — Type-space invariance under elementary substructures.**

    def CompleteTypeOverSet.equivOfElementarySubstructure
        (S : L.ElementarySubstructure M) {A : Set M} (hAS : A ⊆ S) :
        L.CompleteTypeOverSet (M := M) A (Fin 1) ≃
          L.CompleteTypeOverSet (M := ↥S) A' (Fin 1)

where `A' : Set S` is the preimage of `A` under the substructure coercion.

Proof strategy: first show finite realizability is invariant when all
parameters already lie in `S`, then package the resulting equivalence on
complete types.

### Suggested Implementation Order

Implemented so far:

1. **L2.1a-L2.1c** — Package the low-level `Set.univ` language equivalence,
   the canonical expansion compatibility on `M`, and the sentence-/theory-level
   transport lemmas in `LanguageMapOnUniv.lean`.

Remaining dependency order:

1. **L2.2** — Build the comparison between `CompleteTypeOver` and
   `CompleteTypeOverSet` at `Set.univ`.
2. **L2.3** — Recover the bundled-model countability theorem as a corollary.
3. **L3.1, L3.2** — Implement restriction along parameter inclusion and its
   surjectivity.
4. **L3.3** — Reintroduce over-model restriction as a derived map.
5. **L4.1, L4.2** — Package the elementary-substructure transport lemmas for
   later phases.

### Optional Extensions (not acceptance criteria)

- [ ] Prove explicit equivalence with the old bundled-model formulation under
      additional hypotheses, when that comparison is needed later.
- [ ] Invariance of `IsOmegaStable` under language isomorphism.
- [ ] Countability of *realized* complete `1`-types over countable bases.
- [ ] First isolated-type definitions and connection to the Stone topology.

---

## Existing Implementation Relevant to This Phase

The current phase should respect the following implemented content.

### Model-theory layer

- [x] `PartialType`, `PartialTypeOver`, and realization in elementary
      extensions.
- [x] `CompleteType`, `typeOf`, and the bridge from local partial-type API to
      Mathlib's complete-type API.
- [x] `BaseTypes.lean` with the first over-model and over-parameter-set
      complete-type aliases and realization maps.
- [x] `LanguageMapOnUniv.lean` with the canonical language equivalence
      `L[[M]] ≃ᴸ L[[Set.univ : Set M]]`, together with the associated
      expansion, sentence, theory, and complete-theory transport lemmas.
- [x] `Theory.IsOmegaStable` in its parameter-set formulation, together with
      the first countability corollary over subsets of countable models.

### Mathlib bridge to use in this phase

- [x] `Equiv.Set.univ` for the canonical equivalence between `M` and
      `Set.univ : Set M`.
- [x] `Language.lhomWithConstantsMap` and
      `Language.constantsOnMap_isExpansionOn` for the full-parameter-set
      comparison.
- [x] `LHom.realize_onSentence` and `LHom.onTheory_model` for the semantic
      transport attached to L2.1.
- [x] `Language.exists_elementarySubstructure_card_eq` for the countable
      elementary-submodel step.
- [x] `ElementarySubstructure.subtype` for the ambient elementary embedding.
- [x] `ElementarySubstructure.toModel` for repackaging an elementary
      submodel as a bundled model of `T`.
- [x] `Theory.ModelType.shrink` and `Theory.ModelType.ulift` if the remaining
      theorem layer needs explicit universe management.

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
- [ ] Do not build countable-language or completeness hypotheses into the
      primitive definition of `IsOmegaStable`.
- [ ] Do not keep the bundled-model formulation as primitive merely because
      it is easier to integrate with the existing universes.
- [ ] Do not treat the Cantor-Bendixson API as the main path to Morley's
      theorem.
- [ ] Do not reopen the completed Phase 0, Phase 1, or Phase 2 work except
      for minimal supporting lemmas.

## Acceptance Criteria

- [x] `StabilityTheory/ModelTheory/OmegaStable.lean` exists.
- [x] The repository has an explicit base-dependent interface for complete
      `1`-types over bundled models and over parameter sets.
- [x] `IsOmegaStable` is defined without Morley rank, using countable
      parameter sets as the primitive quantification domain.
- [x] The primitive definition does not bake in countable-language or
      completeness assumptions.
- [x] Countability of types over any subset of a countable model is recovered
      immediately from the parameter-set definition.
- [ ] Countability of complete `1`-types over countable bundled models is
      recovered as a derived theorem from the parameter-set definition.
- [ ] The first restriction and change-of-base lemmas are proved.
- [ ] The plan stays aligned with the existing `CompleteType` and topology API
      while leaving Morley rank for the later post-categoricity phase.
