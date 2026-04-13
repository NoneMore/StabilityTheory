import StabilityTheory.ModelTheory.LanguageMapOnUniv

open Set

namespace FirstOrder

namespace Language

universe u v w w'

/-!
# Complete types over `M` versus over `Set.univ`

This file drafts the L2.2 comparison layer from `PLAN.md`. It sits above the
low-level language equivalence packaged in `LanguageMapOnUniv.lean` and
prepares the eventual proof that complete types over a bundled model agree
with complete types over the full parameter set of that model.
-/

namespace LEquiv

variable {L L' : Language.{u, v}} (φ : L ≃ᴸ L') (α : Type w)

/-- The forward language map of a language equivalence is injective on each symbol type. -/
theorem toLHom_injective : φ.toLHom.Injective where
  onFunction := by
    intro n
    refine Function.HasLeftInverse.injective ⟨φ.invLHom.onFunction (n := n), ?_⟩
    intro f
    simpa using congrFun (congrFun (LHom.funext_iff.mp φ.left_inv).1 n) f
  onRelation := by
    intro n
    refine Function.HasLeftInverse.injective ⟨φ.invLHom.onRelation (n := n), ?_⟩
    intro R
    simpa using congrFun (congrFun (LHom.funext_iff.mp φ.left_inv).2 n) R

/-- The inverse language map of a language equivalence is injective on each symbol type. -/
theorem invLHom_injective : φ.invLHom.Injective where
  onFunction := by
    intro n
    refine Function.HasLeftInverse.injective ⟨φ.toLHom.onFunction (n := n), ?_⟩
    intro f
    simpa using congrFun (congrFun (LHom.funext_iff.mp φ.right_inv).1 n) f
  onRelation := by
    intro n
    refine Function.HasLeftInverse.injective ⟨φ.toLHom.onRelation (n := n), ?_⟩
    intro R
    simpa using congrFun (congrFun (LHom.funext_iff.mp φ.right_inv).2 n) R

end LEquiv

namespace Theory

variable {L L' : Language.{u, v}} {T : L.Theory} (φ : L ≃ᴸ L')

/-- Maximal theories transport across a language equivalence. -/
theorem IsMaximal.onTheory_of_equiv (hT : T.IsMaximal) :
    (φ.toLHom.onTheory T).IsMaximal := by
  refine ⟨?_,?_⟩
  · exact (isSatisfiable_onTheory_iff φ.toLHom_injective).2 hT.1
  · intro ψ
    by_cases hψ : ψ ∈ φ.toLHom.onTheory T
    · left; assumption
    · right
      simp only [LHom.mem_onTheory]
      exists φ.symm.onSentence (Formula.not ψ)
      refine ⟨?_,?_⟩
      · have hψ' : φ.symm.onSentence ψ ∉ T := by
          intro hmem
          apply hψ
          rw [LHom.mem_onTheory]
          exact ⟨φ.symm.onSentence ψ, hmem, by
            simpa using (φ.onSentence).apply_symm_apply ψ⟩
        simpa [Formula.not] using (hT.2 (φ.symm.onSentence ψ)).resolve_left hψ'
      · simpa using (φ.onSentence).apply_symm_apply (Formula.not ψ)

end Theory

section CompleteTypeMapOnUniv

variable {L : Language.{u, v}}
variable (M : Type w) [L.Structure M]
variable (α : Type w')

/-- The L2.1 equivalence extended by the extra constants used for type variables. -/
abbrev UnivEquivAddConstants :
    (L[[M]])[[α]] ≃ᴸ (L[[(Set.univ : Set M)]])[[α]] :=
  (L.UnivEquiv M).addConstants α

variable {M α}

/-- The base theory for types over `M` transports to the base theory for types over `Set.univ`. -/
@[simp]
theorem onTheory_elementaryDiagram_UnivEquivAddConstants :
    (L.UnivEquivAddConstants M α).toLHom.onTheory
        (((L[[M]]).lhomWithConstants α).onTheory (L.elementaryDiagram M)) =
      ((L[[(Set.univ : Set M)]].lhomWithConstants α).onTheory
        (L[[(Set.univ : Set M)]].completeTheory M)) := by
  rw [← L.onTheory_completeTheory_UnivEquiv M]
  simpa [UnivEquivAddConstants, Language.LEquiv.addConstants, Language.LEquiv.withConstantsCongr,
    Language.LHom.addConstants, LHom.constantsOnMap_id] using
    ((L.UnivEquiv M).toLHom).onTheory_lhomWithConstants <|
      L.elementaryDiagram M

/-- The inverse extended equivalence transports the full-parameter-set base theory back to the
bundled-model base theory. -/
@[simp]
theorem onTheory_elementaryDiagram_UnivEquivAddConstants_symm :
    ((L.UnivEquivAddConstants M α).symm.toLHom).onTheory
        ((L[[(Set.univ : Set M)]].lhomWithConstants α).onTheory
          (L[[(Set.univ : Set M)]].completeTheory M)) =
      (((L[[M]]).lhomWithConstants α).onTheory (L.elementaryDiagram M)) := by
  rw [← L.onTheory_completeTheory_UnivEquiv_symm M]
  simpa [UnivEquivAddConstants, Language.LEquiv.addConstants, Language.LEquiv.withConstantsCongr,
    Language.LHom.addConstants, LHom.constantsOnMap_id] using
    ((L.UnivEquiv M).symm.toLHom).onTheory_lhomWithConstants <|
      L[[(Set.univ : Set M)]].completeTheory M

namespace CompleteTypeOver

/-- Push a complete type over the bundled model `M` to the full-parameter-set presentation. -/
def toOverSetUniv (p : L.CompleteTypeOver M α) :
    L.CompleteTypeOverSet (Set.univ : Set M) α where
  toTheory := (L.UnivEquivAddConstants M α).toLHom.onTheory p
  subset' := by
    rintro φ ⟨ψ,hMψ,rfl⟩
    exists (L[[M]].lhomWithConstants α).onSentence ((L.UnivEquiv M).symm.onSentence ψ)
    refine ⟨?_,?_⟩
    · apply p.subset'
      simp only [LEquiv.onSentence_apply, LEquiv.symm_toLHom, LHom.mem_onTheory, mem_completeTheory]
      exists (L.UnivEquiv M).symm.onSentence ψ
      refine ⟨?_,?_⟩
      · rwa [realize_onSentence_UnivEquiv_symm]
      · simp
    · simp only [LHom.onSentence, LHom.onFormula, UnivEquivAddConstants,
        LEquiv.toLHom_addConstants, LEquiv.onSentence_apply, LEquiv.symm_toLHom]
      rw [← Function.comp_apply (f := (L[[M]].lhomWithConstants α).onBoundedFormula),
        ← LHom.comp_onBoundedFormula, ← Function.comp_apply
        (f := (LHom.addConstants α (L.UnivEquiv M).toLHom).onBoundedFormula),
        ← LHom.comp_onBoundedFormula, ← LHom.comp_assoc]
      simp only [(L.UnivEquiv M).toLHom.addConstants_comp_lhomWithConstants, LHom.comp_assoc,
        LEquiv.right_inv, LHom.comp_id]
  isMaximal' := p.isMaximal.onTheory_of_equiv <| L.UnivEquivAddConstants M α

end CompleteTypeOver

namespace CompleteTypeOverSet

/-- Pull a complete type over the full parameter set back to the bundled-model presentation. -/
def toOverModelUniv (p : L.CompleteTypeOverSet (Set.univ : Set M) α) :
    L.CompleteTypeOver M α where
  toTheory := ((L.UnivEquivAddConstants M α).symm.toLHom).onTheory p
  subset' := by
    rintro φ ⟨ψ,hMψ,rfl⟩
    exists (L[[↑univ]].lhomWithConstants α).onSentence ((L.UnivEquiv M).onSentence ψ)
    refine ⟨?_,?_⟩
    · apply p.subset'
      simp only [LEquiv.onSentence_apply, LHom.mem_onTheory, mem_completeTheory]
      exists (L.UnivEquiv M).onSentence ψ
      refine ⟨?_,?_⟩
      · rwa [realize_onSentence_UnivEquiv]
      · simp
    · simp only [LHom.onSentence, LHom.onFormula, UnivEquivAddConstants, LEquiv.symm_toLHom,
      LEquiv.invLHom_addConstants, LEquiv.onSentence_apply]
      rw [← Function.comp_apply (f := (L[[↑univ]].lhomWithConstants α).onBoundedFormula),
        ← LHom.comp_onBoundedFormula, ← Function.comp_apply
        (f := (LHom.addConstants α (L.UnivEquiv M).invLHom).onBoundedFormula),
        ← LHom.comp_onBoundedFormula, ← LHom.comp_assoc]
      simp only [(L.UnivEquiv M).invLHom.addConstants_comp_lhomWithConstants, LHom.comp_assoc,
        LEquiv.left_inv, LHom.comp_id]
  isMaximal' := by
    exact Theory.IsMaximal.onTheory_of_equiv
      (φ := (L.UnivEquivAddConstants M α).symm) p.isMaximal

end CompleteTypeOverSet

namespace CompleteTypeOver

variable (L M α)

/-- The canonical comparison between complete types over `M` and over `Set.univ : Set M`. -/
def equivOverSetUniv :
    L.CompleteTypeOver M α ≃
      L.CompleteTypeOverSet (Set.univ : Set M) α where
  toFun := fun p => p.toOverSetUniv
  invFun := fun p => p.toOverModelUniv
  left_inv := by
    intro p
    apply SetLike.ext
    intro φ
    change φ ∈ ((L.UnivEquivAddConstants M α).symm.toLHom).onTheory
      ((L.UnivEquivAddConstants M α).toLHom.onTheory p) ↔ _
    simp only [LEquiv.symm_toLHom, LHom.onTheory_comp,
      LEquiv.left_inv, LHom.id_onTheory, SetLike.mem_coe]
  right_inv := by
    intro p
    apply SetLike.ext
    intro φ
    change φ ∈ ((L.UnivEquivAddConstants M α).toLHom).onTheory
      ((L.UnivEquivAddConstants M α).symm.toLHom.onTheory p) ↔ _
    simp only [LEquiv.symm_toLHom, LHom.onTheory_comp,
      LEquiv.right_inv, LHom.id_onTheory, SetLike.mem_coe]

variable {L M α}

@[simp]
theorem equivOverSetUniv_apply (p : L.CompleteTypeOver M α) :
    p.equivOverSetUniv L M α  = p.toOverSetUniv  :=
  rfl

@[simp]
theorem equivOverSetUniv_symm_apply (p : L.CompleteTypeOverSet (Set.univ : Set M) α) :
    (CompleteTypeOver.equivOverSetUniv L M α).symm p = p.toOverModelUniv :=
  rfl

end CompleteTypeOver

end CompleteTypeMapOnUniv

end Language

end FirstOrder
