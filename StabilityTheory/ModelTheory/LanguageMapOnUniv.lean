import StabilityTheory.ModelTheory.LanguageMap
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

/-- The canonical language equivalence between constants for `M` and constants for
`Set.univ : Set M`. -/
abbrev UnivEquiv : L[[M]] ≃ᴸ L[[(Set.univ : Set M)]] :=
  (LEquiv.refl L).withConstantsCongr (Equiv.Set.univ M).symm

variable [L.Structure M]

/-- The forward map of `UnivEquiv` is an expansion on the ambient structure `M`. -/
instance UnivEquiv_toLHom_isExpansionOn :
    (L.UnivEquiv M).toLHom.IsExpansionOn M := by
  change (L.lhomWithConstantsMap (Equiv.Set.univ M).symm).IsExpansionOn M
  haveI : (LHom.constantsOnMap ⇑(Equiv.Set.univ M).symm).IsExpansionOn M :=
    constantsOnMap_isExpansionOn rfl
  exact LHom.sumMap_isExpansionOn (LHom.id L) (LHom.constantsOnMap ⇑(Equiv.Set.univ M).symm) M

/-- The inverse map of `UnivEquiv` is an expansion on the ambient structure `M`. -/
instance UnivEquiv_symm_toLHom_isExpansionOn :
    (L.UnivEquiv M).symm.toLHom.IsExpansionOn M := by
  change (L.lhomWithConstantsMap (Equiv.Set.univ M)).IsExpansionOn M
  haveI : (LHom.constantsOnMap ⇑(Equiv.Set.univ M)).IsExpansionOn M :=
    constantsOnMap_isExpansionOn rfl
  exact LHom.sumMap_isExpansionOn (LHom.id L) (LHom.constantsOnMap ⇑(Equiv.Set.univ M)) M

/-- Sentence realizability is preserved by `UnivEquiv`. -/
@[simp]
theorem realize_onSentence_UnivEquiv (φ : L[[M]].Sentence) :
    M ⊨ (L.UnivEquiv M).onSentence φ ↔ M ⊨ φ :=
  LHom.realize_onSentence M (L.UnivEquiv M).toLHom φ

/-- Sentence realizability is preserved by the inverse of `UnivEquiv`. -/
@[simp]
theorem realize_onSentence_UnivEquiv_symm
    (φ : L[[(Set.univ : Set M)]].Sentence) :
    M ⊨ (L.UnivEquiv M).symm.onSentence φ ↔ M ⊨ φ :=
  LHom.realize_onSentence M (L.UnivEquiv M).symm.toLHom φ

/-- Modelhood is preserved by the forward map of `UnivEquiv`. -/
@[simp]
theorem onTheory_model_UnivEquiv (T : L[[M]].Theory) :
    M ⊨ (L.UnivEquiv M).toLHom.onTheory T ↔ M ⊨ T :=
  LHom.onTheory_model (L.UnivEquiv M).toLHom T

/-- Modelhood is preserved by the inverse map of `UnivEquiv`. -/
@[simp]
theorem onTheory_model_UnivEquiv_symm (T : L[[(Set.univ : Set M)]].Theory) :
    M ⊨ (L.UnivEquiv M).symm.toLHom.onTheory T ↔ M ⊨ T :=
  LHom.onTheory_model (L.UnivEquiv M).symm.toLHom T

/-- Transporting the complete theory of `M` along the forward map gives the complete theory in
the full-parameter-set language. -/
@[simp]
theorem onTheory_completeTheory_UnivEquiv :
    (L.UnivEquiv M).toLHom.onTheory (L.elementaryDiagram M) =
      L[[(Set.univ : Set M)]].completeTheory M := by
  ext φ
  constructor
  · rintro ⟨φ₀, hφ₀, rfl⟩
    exact (L.realize_onSentence_UnivEquiv M φ₀).2 (by simpa using hφ₀)
  · intro hφ
    refine ⟨(L.UnivEquiv M).symm.onSentence φ, ?_, ?_⟩
    · exact (L.realize_onSentence_UnivEquiv_symm M φ).2 (by simpa using hφ)
    · simpa using (L.UnivEquiv M).onSentence.apply_symm_apply φ

/-- Transporting the complete theory of `M` along the inverse map gives the complete theory in
the bundled-model language. -/
@[simp]
theorem onTheory_completeTheory_UnivEquiv_symm :
    (L.UnivEquiv M).symm.toLHom.onTheory
        (L[[(Set.univ : Set M)]].completeTheory M) =
      L.elementaryDiagram M := by
  ext φ
  constructor
  · rintro ⟨φ₀, hφ₀, rfl⟩
    exact (L.realize_onSentence_UnivEquiv_symm M φ₀).2 (by simpa using hφ₀)
  · intro hφ
    refine ⟨(L.UnivEquiv M).onSentence φ, ?_, ?_⟩
    · exact (L.realize_onSentence_UnivEquiv M φ).2 (by simpa using hφ)
    · simpa using (L.UnivEquiv M).onSentence.symm_apply_apply φ

end LanguageMapOnUniv

end Language

end FirstOrder
