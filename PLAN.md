# Plan

This file tracks the active short-term plan.  The current phase remains the
omega-stability interface layer.  The over-model and over-parameter-set type
spaces (`CompleteTypeOver`, `CompleteTypeOverSet`) compile, the primitive
definition of `IsOmegaStable` uses parameter sets, and the canonical
comparison between types over `M` and over `Set.univ : Set M` is now
implemented.  The remaining work is the surjectivity and derived over-model
parts of the restriction layer, the elementary-substructure transport lemmas,
and then the final comparison with the usual bundled-model formulation in the
countable-language complete-theory setting.

Current snapshot:
- Phase 0, Phase 1, and Phase 2 are complete.
- `BaseTypes.lean` already provides `CompleteTypeOver`,
  `CompleteTypeOverSet`, `typeOfOver`, `typeOfOverSet`, and
  `liftParamsToPartial`.
- `OmegaStable.lean` already uses the parameter-set-based definition of
  `Theory.IsOmegaStable` and proves the first countability corollary over
  subsets of countable models.
- `LanguageMapOnUniv.lean` now packages the low-level comparison between
  `L[[M]]` and `L[[Set.univ : Set M]]`, including `UnivEquiv`, the two
  `IsExpansionOn` instances on `M`, and the sentence-, theory-, and
  complete-theory transport lemmas attached to this canonical equivalence.
- `LanguageMap.lean` now also contains the small `onTheory` composition and
  identity lemmas, together with the `addConstants` simp lemmas for language
  equivalences, that support the complete-type comparison proofs.
- `CompleteTypeMapOnUniv.lean` now packages the added-constants base-theory
  transport lemmas, the forward and inverse maps
  `CompleteTypeOver.toOverSetUniv` and
  `CompleteTypeOverSet.toOverModelUniv`, and the resulting equivalence
  `CompleteTypeOver.equivOverSetUniv`.
- `OmegaStable.lean` now also defines restriction of complete types along
  parameter inclusions, together with the supporting language-map lemmas
  `restrictLHom`, `restrictLHom_injective`, and
  `onTheory_completeTheory_mono`.
- The intended counted type spaces for `omega`-stability are complete `1`-types
  `L.CompleteTypeOverSet A (Fin 1)` over countable parameter sets `A`.
- Over-model type spaces `L.CompleteTypeOver M (Fin 1)` remain part of the
  local interface, but they should be treated as a derived companion
  formulation rather than the primitive definition.
- No local file yet for isolated types, strongly minimal sets, saturated
  models, or prime models.
- The remaining Phase 3 work in `OmegaStable.lean` is now the surjectivity
  and over-model companion to restriction, then the first
  elementary-substructure transport lemmas, and finally the
  countable-language complete-theory comparison theorem for the bundled-model
  formulation.

## Phase 3: Parameterized Types and Omega-Stability

Goal:
- [x] Introduce the first explicit local API for complete types over bundled
      base models and over parameter sets inside those models.
- [x] Fix the counted type spaces in the first implementation to be complete
      `1`-types, with `Fin 1` as the arity convention.
- [x] Redefine `IsOmegaStable` by countability of complete `1`-types over
      countable parameter sets, without going through Morley rank or total
      transcendence.
- [ ] Recover the usual bundled-model formulation as an equivalent
      reformulation under the countable-language and complete-theory
      hypotheses used in the classical textbook definition.
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

## Current Priority: Restriction Maps and Elementary-Substructure Transport

The over-model and over-parameter-set type spaces are in place, the primitive
`IsOmegaStable` definition has been revised, and the `Set.univ` comparison is
now packaged both at the language level and at the complete-type level.  The
next bottleneck is therefore the rest of the first change-of-base layer on top
of that equivalence: prove surjectivity of restriction, package the derived
over-model restriction map, and then package the elementary-substructure
transport needed to move countable parameter sets into countable ambient
models.  The comparison with the usual bundled-model formulation should be
deferred until those ingredients are available.

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

Status: L2.1 and L2.2 are implemented in `LanguageMapOnUniv.lean` and
`CompleteTypeMapOnUniv.lean`.  The full-parameter-set comparison layer itself
is complete; the final bundled-model comparison theorem is deferred to the end
of the phase.

The over-model space `L.CompleteTypeOver M (Fin 1)` should remain available,
but only as a derived reformulation of types over the full parameter set of
`M`.

Packaging note:
- The low-level with-constants equivalence and its canonical semantic
  compatibility should live below the complete-type API.
- The induced equivalence on complete types should live in the base-change
  layer built on top of that low-level interface.
- The forward bundled-model countability corollary and the final comparison
  theorem for `IsOmegaStable` should remain in `OmegaStable.lean`.

**L2.1 — Compare constants for `M` with constants for `Set.univ : Set M`.**

Status: implemented in `LanguageMapOnUniv.lean`.

Package the obvious bijection between `M` and `Set.univ : Set M` into the
corresponding language equivalence between `L[[M]]` and `L[[Set.univ]]`.
This layer should not stop at a bare `LEquiv`: in the canonical expansions on
the ambient structure `M`, it should also package the induced semantic
compatibility.

Expected deliverables:

    def UnivEquiv :
        L[[M]] ≃ᴸ L[[Set.univ : Set M]]

using `Equiv.Set.univ M` and `LEquiv.withConstantsCongr`.

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
- `LanguageMapOnUniv.lean` defines `UnivEquiv`.
- It proves the two `IsExpansionOn` instances on `M`, the sentence- and
  theory-level transport lemmas, and the two complete-theory transport lemmas.

**L2.2 — Transport complete types across that language equivalence.**

Status: implemented in `CompleteTypeMapOnUniv.lean`.

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

Implemented content:
- `CompleteTypeMapOnUniv.lean` packages
  `Theory.IsMaximal.onTheory_of_equiv`, the added-constants elementary-diagram
  transport lemmas in both directions, the maps `toOverSetUniv` and
  `toOverModelUniv`, and the equivalence `equivOverSetUniv`.
- `LanguageMap.lean` now provides the auxiliary `LHom.onTheory_comp`,
  `LHom.id_onTheory`, and `LEquiv.addConstants` simp lemmas used to prove the
  inverse laws for `equivOverSetUniv`.

### L3. Restriction Maps and Monotonicity

File: `OmegaStable.lean`.  Builds on: `PartialTypes.lean` compactness, L1, L2.

Status: L3.1 is implemented in `OmegaStable.lean`; L3.2 and L3.3 remain.

With the parameter-set formulation primitive, the first change-of-base map
should be restriction along inclusion of parameter sets.

**L3.1 — Restriction of complete types along parameter inclusion.**

    def CompleteTypeOverSet.restrict {A B : Set M} (hAB : A ⊆ B) :
        L.CompleteTypeOverSet (M := M) B (Fin 1) →
          L.CompleteTypeOverSet (M := M) A (Fin 1)

Pull back along the map `L.lhomWithConstantsMap` induced by the inclusion
`A ↪ B`.

Implemented content:
- `OmegaStable.lean` defines the auxiliary language map `restrictLHom`,
  proves `restrictLHom_injective`, proves the base-theory monotonicity lemma
  `onTheory_completeTheory_mono`, and packages the resulting map
  `CompleteTypeOverSet.restrict`.

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
2. **L2.2** — Build the comparison between `CompleteTypeOver` and
   `CompleteTypeOverSet` at `Set.univ` in `CompleteTypeMapOnUniv.lean`.
3. **L3.1** — Implement restriction of complete types along parameter
   inclusion in `OmegaStable.lean`.

Remaining dependency order:

1. **L3.2** — Prove surjectivity of restriction along parameter inclusion.
2. **L3.3** — Reintroduce over-model restriction as a derived map.
3. **L4.1, L4.2** — Package the elementary-substructure transport lemmas for
   later phases.
4. **L5.1** — State and prove the countable-language complete-theory
   equivalence with the usual bundled-model formulation.

### Optional Extensions (not acceptance criteria)

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
- [x] `CompleteTypeMapOnUniv.lean` with the canonical comparison between
      `CompleteTypeOver M α` and `CompleteTypeOverSet (Set.univ : Set M) α`.
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
- [x] The canonical equivalence between complete types over `M` and over
      `Set.univ : Set M` is packaged below the `omega`-stability theorem
      layer.
- [x] Restriction of complete types along parameter inclusion is implemented.
- [ ] The remaining surjectivity and change-of-base lemmas are proved.
- [ ] In the countable-language complete-theory setting, the primitive
      parameter-set definition is proved equivalent to the usual bundled-model
      formulation.
- [ ] The plan stays aligned with the existing `CompleteType` and topology API
      while leaving Morley rank for the later post-categoricity phase.

## Final Comparison Theorem

The old one-way bundled-model countability corollary is better treated as the
forward implication of the end-of-phase comparison theorem, since the reverse
direction depends on the restriction and elementary-substructure transport
lemmas from L3 and L4.

### L5.1 — Equivalent bundled-model formulation in the countable complete setting

File: `OmegaStable.lean`.  Builds on: L2, L3, L4, and
`Mathlib.ModelTheory.Satisfiability`.

    theorem Theory.isOmegaStable_iff_countable_typeOver_of_countable
        (hL : L.card ≤ ℵ₀) (hT : T.IsComplete) :
        T.IsOmegaStable ↔
          ∀ (M : T.ModelType), Countable M →
            Countable (L.CompleteTypeOver M (Fin 1))

This should be the explicit comparison theorem that justifies the familiar
countable complete-theory packaging of `omega`-stability while keeping the
parameter-set formulation primitive in the repository.

Proof strategy:
- Forward direction: apply `T.IsOmegaStable` at `A = Set.univ`, then transport
  along `CompleteTypeOver.equivOverSetUniv`.  The old bundled-model
  countability corollary can be recorded as this implication or as an
  immediately extracted helper lemma.
- Reverse direction: given a countable parameter set `A : Set M`, first split
  off the finite-model case if needed.  In the infinite case, use L4.1 to
  place `A` inside a countable elementary submodel `S`, transport the type
  space over `A` from `M` to `S` via L4.2, apply the bundled-model hypothesis
  to `S`, and descend along the surjective restriction map from L3.

Implementation note:
- The theorem should state the countable-language hypothesis explicitly.
- The proof should isolate precisely where completeness is used, rather than
  baking it back into the primitive definition.
