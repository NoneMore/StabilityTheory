import StabilityTheory.ModelTheory.BaseTypes

/-!
# Language maps on `Set.univ`

This file packages the low-level L2.1 comparison between `L[[M]]` and
`L[[Set.univ : Set M]]`, together with the associated sentence- and
theory-level transport lemmas.
-/

namespace FirstOrder

namespace Language

universe u v w

section LanguageMapOnUniv

variable (L : Language.{u, v})
variable (M : Type w)

/-- The forward language map from constants indexed by `M` to constants indexed by `Set.univ`. -/
abbrev withConstantsMapToUniv : L[[M]] →ᴸ L[[(Set.univ : Set M)]] :=
  L.lhomWithConstantsMap (Equiv.Set.univ M).symm

/-- The inverse language map from constants indexed by `Set.univ` back to constants indexed by
`M`. -/
abbrev withConstantsMapFromUniv : L[[(Set.univ : Set M)]] →ᴸ L[[M]] :=
  L.lhomWithConstantsMap (Equiv.Set.univ M)

section LHom

variable {L' L'' L₁ L₂ L₃ L₄ : Language}

/-- The identity map on a sum language is the sum of the identity maps on the two factors. -/
theorem LHom.id_sumMap_id (L : Language.{u, v}) (L' : Language) :
    LHom.id (L.sum L') = (LHom.id L).sumMap (LHom.id L') := by
  apply LHom.funext
  · ext _ f; cases f <;> simp
  · ext _ R; cases R <;> simp

/-- Composition of sum-language maps is computed componentwise. -/
theorem LHom.sumMap_comp_sumMap (φ₂ : L' →ᴸ L'') (ψ₂ : L₃ →ᴸ L₄) (φ₁ : L →ᴸ L')
    (ψ₁ : L₁ →ᴸ L₃) :
    (φ₂.sumMap ψ₂).comp (φ₁.sumMap ψ₁) = (φ₂.comp φ₁).sumMap (ψ₂.comp ψ₁) := by
  apply LHom.funext
  · ext _ f; cases f <;> simp
  · ext _ R; cases R <;> simp

/-- Composition of maps between constant languages is induced by function composition on the
index types. -/
theorem LHom.constantsOnMap_comp {α β γ : Type*} (f : α → β) (g : β → γ) :
    (LHom.constantsOnMap g).comp (LHom.constantsOnMap f) = LHom.constantsOnMap (g ∘ f) := by
  refine LHom.funext ?_ rfl
  ext n c
  cases n with
  | zero => simp [constantsOnMap]
  | succ => cases c

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

end LHom

@[simp]
theorem withConstantsMapFromUniv_comp_toUniv :
    (L.withConstantsMapFromUniv M).comp
        (L.withConstantsMapToUniv M) =
      LHom.id L[[M]] := by
  simp only [withConstants]
  trans (LHom.id L).sumMap (LHom.id (constantsOn M))
  · simp only [withConstantsMapFromUniv, lhomWithConstantsMap, withConstantsMapToUniv,
      LHom.sumMap_comp_sumMap, LHom.constantsOnMap_comp, LHom.constantsOnMap_id,
      LHom.comp_id, _root_.Equiv.self_comp_symm]
  · exact Eq.symm (LHom.id_sumMap_id L (constantsOn M))

@[simp]
theorem withConstantsMapToUniv_comp_fromUniv :
    (L.withConstantsMapToUniv M).comp
        (L.withConstantsMapFromUniv M) =
      LHom.id L[[(Set.univ : Set M)]] := by
  simp only [withConstants]
  trans (LHom.id L).sumMap (LHom.id (constantsOn (Set.univ : Set M)))
  · simp only [withConstantsMapFromUniv, lhomWithConstantsMap, withConstantsMapToUniv,
      LHom.sumMap_comp_sumMap, LHom.constantsOnMap_comp, LHom.constantsOnMap_id,
      LHom.comp_id, _root_.Equiv.symm_comp_self]
  · exact Eq.symm (LHom.id_sumMap_id L (constantsOn (Set.univ : Set M)))

/-- The canonical language equivalence between constants for `M` and constants for
`Set.univ : Set M`. -/
def withConstantsEquivUniv : L[[M]] ≃ᴸ L[[(Set.univ : Set M)]] where
  toLHom := L.withConstantsMapToUniv M
  invLHom := L.withConstantsMapFromUniv M
  left_inv := L.withConstantsMapFromUniv_comp_toUniv M
  right_inv := L.withConstantsMapToUniv_comp_fromUniv M

variable [L.Structure M]

/-- The forward comparison map is an expansion on the ambient structure `M`. -/
instance withConstantsMapToUniv_isExpansionOn :
    (L.withConstantsMapToUniv M).IsExpansionOn M := by
  simp only [withConstantsMapToUniv, lhomWithConstantsMap]
  haveI : (LHom.constantsOnMap ⇑(Equiv.Set.univ M).symm).IsExpansionOn M :=
    constantsOnMap_isExpansionOn rfl
  exact LHom.sumMap_isExpansionOn (LHom.id L) (LHom.constantsOnMap ⇑(Equiv.Set.univ M).symm) M

/-- The inverse comparison map is an expansion on the ambient structure `M`. -/
instance withConstantsMapFromUniv_isExpansionOn :
    (L.withConstantsMapFromUniv M).IsExpansionOn M := by
  simp only [withConstantsMapFromUniv, lhomWithConstantsMap]
  haveI : (LHom.constantsOnMap ⇑(Equiv.Set.univ M)).IsExpansionOn M :=
    constantsOnMap_isExpansionOn rfl
  exact LHom.sumMap_isExpansionOn (LHom.id L) (LHom.constantsOnMap ⇑(Equiv.Set.univ M)) M

/-- Sentence realizability is preserved by the forward full-parameter comparison map. -/
@[simp]
theorem realize_onSentence_withConstantsMapToUniv (φ : L[[M]].Sentence) :
    M ⊨ (L.withConstantsMapToUniv M).onSentence φ ↔ M ⊨ φ :=
  LHom.realize_onSentence M (L.withConstantsMapToUniv M) φ

/-- Sentence realizability is preserved by the inverse full-parameter comparison map. -/
@[simp]
theorem realize_onSentence_withConstantsMapFromUniv
    (φ : L[[(Set.univ : Set M)]].Sentence) :
    M ⊨ (L.withConstantsMapFromUniv M).onSentence φ ↔ M ⊨ φ :=
  LHom.realize_onSentence M (L.withConstantsMapFromUniv M) φ

/-- Modelhood is preserved by the forward full-parameter comparison map. -/
@[simp]
theorem onTheory_model_withConstantsMapToUniv (T : L[[M]].Theory) :
    M ⊨ (L.withConstantsMapToUniv M).onTheory T ↔ M ⊨ T :=
  LHom.onTheory_model (L.withConstantsMapToUniv M) T

/-- Modelhood is preserved by the inverse full-parameter comparison map. -/
@[simp]
theorem onTheory_model_withConstantsMapFromUniv (T : L[[(Set.univ : Set M)]].Theory) :
    M ⊨ (L.withConstantsMapFromUniv M).onTheory T ↔ M ⊨ T :=
  LHom.onTheory_model (L.withConstantsMapFromUniv M) T

/-- Transporting the complete theory of `M` along the forward map gives the complete theory in
the full-parameter-set language. -/
@[simp]
theorem onTheory_completeTheory_withConstantsMapToUniv :
    (L.withConstantsMapToUniv M).onTheory (L[[M]].completeTheory M) =
      L[[(Set.univ : Set M)]].completeTheory M := by
  ext φ
  constructor
  · rintro ⟨φ₀, hφ₀, rfl⟩
    exact (L.realize_onSentence_withConstantsMapToUniv M φ₀).2 (by simpa using hφ₀)
  · intro hφ
    refine ⟨(L.withConstantsEquivUniv M).symm.onSentence φ, ?_, ?_⟩
    · change M ⊨ (L.withConstantsMapFromUniv M).onSentence φ
      exact (L.realize_onSentence_withConstantsMapFromUniv M φ).2 (by simpa using hφ)
    · simpa [withConstantsEquivUniv] using
        (L.withConstantsEquivUniv M).onSentence.apply_symm_apply φ

/-- Transporting the complete theory of `M` along the inverse map gives the complete theory in
the bundled-model language. -/
@[simp]
theorem onTheory_completeTheory_withConstantsMapFromUniv :
    (L.withConstantsMapFromUniv M).onTheory
        (L[[(Set.univ : Set M)]].completeTheory M) =
      L[[M]].completeTheory M := by
  ext φ
  constructor
  · rintro ⟨φ₀, hφ₀, rfl⟩
    exact (L.realize_onSentence_withConstantsMapFromUniv M φ₀).2 (by simpa using hφ₀)
  · intro hφ
    refine ⟨(L.withConstantsEquivUniv M).onSentence φ, ?_, ?_⟩
    · change M ⊨ (L.withConstantsMapToUniv M).onSentence φ
      exact (L.realize_onSentence_withConstantsMapToUniv M φ).2 (by simpa using hφ)
    · simpa [withConstantsEquivUniv] using
        (L.withConstantsEquivUniv M).onSentence.symm_apply_apply φ

end LanguageMapOnUniv

end Language

end FirstOrder
