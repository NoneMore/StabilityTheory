import Mathlib.ModelTheory.Syntax

/-!
# Supplemental language-map API

This file collects generic language-map constructions that extend
`Mathlib/ModelTheory/LanguageMap`. It is intentionally named to align with the
upstream module and to make future upstream migration straightforward.
-/

namespace FirstOrder

namespace Language

universe u v u' v'

section LHom

variable {L L' L'' L₁ L₂ L₃ L₄ : Language}
variable {α : Type*}

/-- The identity map on a sum language is the sum of the identity maps on the two factors. -/
theorem LHom.id_sumMap_id (L : Language.{u, v}) (L' : Language.{u', v'}) :
    LHom.id (L.sum L') = (LHom.id L).sumMap (LHom.id L') := by
  apply LHom.funext
  · ext _ f
    cases f <;> simp
  · ext _ R
    cases R <;> simp

/-- The identity language homomorphism is injective. -/
theorem LHom.id_injective (L : Language.{u, v}) : (LHom.id L).Injective :=
  ⟨fun h => h, fun h => h⟩

/-- Composition of sum-language maps is computed componentwise. -/
theorem LHom.sumMap_comp_sumMap (φ₂ : L' →ᴸ L'') (ψ₂ : L₃ →ᴸ L₄) (φ₁ : L →ᴸ L')
    (ψ₁ : L₁ →ᴸ L₃) :
    (φ₂.sumMap ψ₂).comp (φ₁.sumMap ψ₁) = (φ₂.comp φ₁).sumMap (ψ₂.comp ψ₁) := by
  apply LHom.funext
  · ext _ f
    cases f <;> simp
  · ext _ R
    cases R <;> simp

/-- If two language homomorphisms are injective, then their sum-language map is injective. -/
theorem LHom.sumMap_injective {φ : L →ᴸ L'} {ψ : L₁ →ᴸ L₂}
    (hφ : φ.Injective) (hψ : ψ.Injective) : (φ.sumMap ψ).Injective :=
  ⟨by
      intro n
      exact Sum.map_injective.2 ⟨hφ.onFunction, hψ.onFunction⟩,
    by
      intro n
      exact Sum.map_injective.2 ⟨hφ.onRelation, hψ.onRelation⟩⟩

/-- Composition of maps between constant languages is induced by function composition on the
index types. -/
theorem LHom.constantsOnMap_comp {α β γ : Type*} (f : α → β) (g : β → γ) :
    (LHom.constantsOnMap g).comp (LHom.constantsOnMap f) = LHom.constantsOnMap (g ∘ f) := by
  refine LHom.funext ?_ rfl
  ext n c
  cases n with
  | zero => simp [constantsOnMap]
  | succ => cases c

/-- If the index map is injective, then the induced map on constant languages is injective. -/
theorem LHom.constantsOnMap_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    (LHom.constantsOnMap f).Injective :=
  ⟨by
      intro n
      cases n with
      | zero => simpa [LHom.constantsOnMap] using hf
      | succ n => exact fun c => isEmptyElim c,
    fun {n} R => isEmptyElim R⟩

/-- The identity map on a constant language is induced by the identity function on the index
type. -/
theorem LHom.constantsOnMap_id (α : Type*) :
    LHom.id (constantsOn α) = LHom.constantsOnMap (id : α → α) := by
  refine LHom.funext ?_ ?_
  · ext n c
    cases n with
    | zero => simp [constantsOnMap]
    | succ => cases c
  · ext _ R
    cases R

/-- Adding constants commutes with the canonical map into the language with constants. -/
theorem LHom.addConstants_comp_lhomWithConstants (f : L →ᴸ L') :
    (f.addConstants α).comp (L.lhomWithConstants α) = (L'.lhomWithConstants α).comp f := by
  ext <;> rfl

/-- Applying `onTheory` along a composite language homomorphism agrees with applying `onTheory`
stepwise. -/
theorem LHom.onTheory_comp (g : L' →ᴸ L'') (f : L →ᴸ L') (T : L.Theory) :
    g.onTheory (f.onTheory T) = (g.comp f).onTheory T := by
  simp only [onTheory, Set.image_image]
  congr with φ
  simp [LHom.onSentence, LHom.onFormula]

/-- Applying `onTheory` along the identity language homomorphism does nothing. -/
theorem LHom.id_onTheory (L : Language.{u, v}) (T : L.Theory) :
    (LHom.id L).onTheory T = T := by
  ext φ
  simp [LHom.mem_onTheory, LHom.onSentence, LHom.onFormula]

/-- Applying `onTheory` after adjoining type-variable constants commutes with language maps. -/
theorem LHom.onTheory_lhomWithConstants (f : L →ᴸ L') (T : L.Theory) :
    (f.addConstants α).onTheory ((L.lhomWithConstants α).onTheory T) =
      (L'.lhomWithConstants α).onTheory (f.onTheory T) := by
  simp [LHom.onTheory_comp]
  congr

end LHom

namespace LEquiv

variable {L L' : Language} (φ : L ≃ᴸ L') {α β : Type*} (e : α ≃ β)

/-- Transport a language equivalence across a reindexing of added constants.

This is a local extension of the `LanguageMap` API and is a natural candidate
for upstreaming. -/
def withConstantsCongr : L[[α]] ≃ᴸ L'[[β]] where
  toLHom := φ.toLHom.sumMap (LHom.constantsOnMap e)
  invLHom := φ.invLHom.sumMap (LHom.constantsOnMap e.symm)
  left_inv := by
    simp only [withConstants, LHom.sumMap_comp_sumMap, LHom.id_sumMap_id]
    congr
    · exact φ.left_inv
    · simpa [LHom.constantsOnMap_comp] using Eq.symm (LHom.constantsOnMap_id α)
  right_inv := by
    simp only [withConstants, LHom.sumMap_comp_sumMap, LHom.id_sumMap_id]
    congr
    · exact φ.right_inv
    · simpa [LHom.constantsOnMap_comp] using Eq.symm (LHom.constantsOnMap_id β)

/-- Add the same auxiliary constants to both sides of a language equivalence. -/
abbrev addConstants (φ : L ≃ᴸ L') (α : Type*) : L[[α]] ≃ᴸ L'[[α]] :=
  φ.withConstantsCongr (_root_.Equiv.refl α)

@[simp]
theorem toLHom_addConstants (φ : L ≃ᴸ L') (α : Type*) :
    (φ.addConstants α).toLHom = φ.toLHom.addConstants α := by
  simp [LEquiv.addConstants, LEquiv.withConstantsCongr, LHom.addConstants, LHom.constantsOnMap_id]

@[simp]
theorem invLHom_addConstants (φ : L ≃ᴸ L') (α : Type*) :
    (φ.addConstants α).invLHom = φ.invLHom.addConstants α := by
  simp [LEquiv.addConstants, LEquiv.withConstantsCongr, LHom.addConstants, LHom.constantsOnMap_id]

end LEquiv

end Language

end FirstOrder
