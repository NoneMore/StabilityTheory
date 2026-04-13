import Mathlib.Data.Set.Countable
import Mathlib.ModelTheory.Skolem
import StabilityTheory.ModelTheory.LanguageMap
import StabilityTheory.ModelTheory.BaseTypes
import StabilityTheory.ModelTheory.Satisfiablity

open Set
open Cardinal

namespace FirstOrder

namespace Language

open FirstOrder.Language

universe u v w w' w''

/-!
# Omega-stability preliminaries

This file currently provides the first `omega`-stability-specific layer for
Phase 3, together with a countable elementary-substructure wrapper.
-/

-- section LowenheimSkolem

-- variable {L : Language.{u, v}} {T : L.Theory}
-- variable {M : Type w} [L.Structure M] [M ⊨ T]

-- /-- A countable parameter set in an infinite model is contained in a countable elementary
-- substructure. -/
-- theorem exists_countable_elementarySubstructure [Infinite M]
--     (hL : L.card ≤ ℵ₀) {A : Set M} (hA : A.Countable) :
--     ∃ S : L.ElementarySubstructure M, A ⊆ S ∧ Countable S := by
--   classical
--   obtain ⟨S, hAS, hS⟩ :=
--     exists_elementarySubstructure_card_eq.{u, v, w, max u v} L A ℵ₀
--       (by simp)
--       (by simpa only [lift_aleph0, ge_iff_le, lift_le_aleph0,
--       le_aleph0_iff_subtype_countable, setOf_mem_eq] using hA)
--       (by simpa using hL)
--       (by simp)
--   simp only [lift_aleph0, lift_eq_aleph0] at hS
--   refine ⟨S, hAS, mk_le_aleph0_iff.mp <| le_of_eq hS⟩

-- end LowenheimSkolem

section RestrictionMaps

variable {L : Language.{u, v}}
variable {M : Type w}
variable {α : Type w'}

namespace LHom

/-- The inclusion-induced map on languages with constants is injective. -/
theorem lhomWithConstantsMap_injective {A B : Set M} (hAB : A ⊆ B) :
    (L.lhomWithConstantsMap (Set.inclusion hAB)).Injective :=
  sumMap_injective (id_injective L) (constantsOnMap_injective (inclusion_injective hAB))

/-- Adding variable-constants preserves injectivity of language maps. -/
theorem addConstants_injective {L' : Language} {β : Type*} {φ : L →ᴸ L'}
    (hφ : φ.Injective) :
    (φ.addConstants β).Injective :=
  sumMap_injective hφ (id_injective (constantsOn β))

end LHom

namespace Theory

/-- Pulling back a maximal theory along an injective language map yields a maximal theory. -/
theorem IsMaximal.preimage {L' : Language} (φ : L →ᴸ L') {T' : L'.Theory} (hT' : T'.IsMaximal) :
    Theory.IsMaximal ({ ψ | φ.onSentence ψ ∈ T' } : L.Theory) := by
  refine ⟨?_,?_⟩
  · let S : L.Theory := {ψ | φ.onSentence ψ ∈ T'}
    suffices h : (φ.onTheory S).IsSatisfiable from
      isSatisfiable_of_isSatisfiable_onTheory φ h
    refine IsSatisfiable.mono hT'.1 ?_
    simp only [LHom.onTheory, image_subset_iff, S]
    exact setOf_subset.mpr fun x a ↦ a
  · intro ϕ
    by_contra!
    exact hT'.1.false_of_mem_of_not_mem ((hT'.mem_or_not_mem (φ.onSentence ϕ)).resolve_right this.2)
      <| (hT'.mem_or_not_mem (φ.onSentence ϕ)).resolve_left this.1

end Theory

/-- The language map used to forget parameters from `B \ A`. -/
abbrev restrictLHom (L : Language.{u, v}) {A B : Set M} (hAB : A ⊆ B) (α : Type w') :
    (L[[A]])[[α]] →ᴸ (L[[B]])[[α]] :=
  (L.lhomWithConstantsMap (Set.inclusion hAB)).addConstants α

namespace CompleteTypeOverSet

/-- The language map used to forget parameters from `B \ A`. -/
abbrev restrictLHom {A B : Set M} (hAB : A ⊆ B) :
    (L[[A]])[[α]] →ᴸ (L[[B]])[[α]] :=
  (L.lhomWithConstantsMap (Set.inclusion hAB)).addConstants α

theorem restrictLHom_injective {A B : Set M} (hAB : A ⊆ B) :
    (L.restrictLHom hAB α).Injective :=
  LHom.addConstants_injective (LHom.lhomWithConstantsMap_injective hAB)

variable [L.Structure M] (L α)

/-- The base theory over `A` maps into the base theory over `B`. -/
theorem onTheory_completeTheory_mono {A B : Set M} (hAB : A ⊆ B) :
    (L.restrictLHom hAB α).onTheory
        (((L[[A]]).lhomWithConstants α).onTheory ((L[[A]]).completeTheory M)) ⊆
      (((L[[B]]).lhomWithConstants α).onTheory ((L[[B]]).completeTheory M)) := by
  rw [LHom.onTheory_comp, Language.restrictLHom,
    LHom.addConstants_comp_lhomWithConstants, ←LHom.onTheory_comp]
  exact Set.image_mono <| by
    rintro _ ⟨ψ, hψ, rfl⟩
    exact (LHom.realize_onSentence M (L.lhomWithConstantsMap (inclusion hAB)) ψ).mpr hψ

/-- Restrict a complete type along an inclusion of parameter sets. -/
def restrict {A B : Set M} (hAB : A ⊆ B) :
    L.CompleteTypeOverSet B α → L.CompleteTypeOverSet A α := fun p =>
      { toTheory := { σ | (L.restrictLHom hAB α).onSentence σ ∈ p }
        subset' := by
          intro φ hφ
          simp only [mem_setOf_eq]
          exact p.subset' <|
            onTheory_completeTheory_mono L α hAB <| by
              exact ⟨φ, hφ, rfl⟩
        isMaximal' := p.isMaximal'.preimage (restrictLHom hAB)}

@[simp]
theorem mem_restrict {A B : Set M} (hAB : A ⊆ B)
    (p : L.CompleteTypeOverSet (M := M) B α) {σ : (L[[A]])[[α]].Sentence} :
    σ ∈ restrict (L := L) (M := M) (α := α) hAB p ↔
      (restrictLHom (L := L) (M := M) (α := α) hAB).onSentence σ ∈ p :=
  Iff.rfl

end CompleteTypeOverSet

end RestrictionMaps

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory)

/-- Parameter-set-based `omega`-stability: every countable parameter set inside a bundled model
has countably many complete `1`-types over it. This is the primitive repository definition for
the current phase. -/
def IsOmegaStable : Prop :=
  ∀ (M : ModelType.{u, v, w} T) (A : Set M),
    A.Countable →
      Countable (L.CompleteTypeOverSet A (Fin 1))

theorem IsOmegaStable.countable_typeOverSet_of_countable
    (hT : IsOmegaStable.{u, v, w} T) (M : ModelType.{u, v, w} T)
    (hM : Countable M) (A : Set M) :
    Countable (L.CompleteTypeOverSet A (Fin 1)) := by
  refine hT M A (to_countable A)

end Theory

end Language

end FirstOrder
