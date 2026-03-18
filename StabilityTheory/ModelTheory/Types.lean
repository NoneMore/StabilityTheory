import Mathlib.ModelTheory.Types
import StabilityTheory.ModelTheory.PartialTypes

open Set FirstOrder.Language.Theory.PartialType

namespace FirstOrder

namespace Language

namespace Theory

universe u v w w'

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

namespace CompleteType

/-- The partial type underlying a complete type. -/
def toPartialType (p : T.CompleteType α) : T.PartialType α :=
  PartialType.ofSet
    {φ | Formula.equivSentence φ ∈ (p : L[[α]].Theory)}
    (by
      refine p.isMaximal.1.mono ?_
      intro φ hφ
      rcases hφ with hφT | ⟨ψ, hψ, rfl⟩
      · exact p.subset hφT
      · exact hψ)

@[simp]
theorem mem_toPartialType
    (p : T.CompleteType α) {φ : L.Formula α} :
    φ ∈ p.toPartialType ↔ Formula.equivSentence φ ∈ p := by
  simp [toPartialType]
  rfl

theorem toPartialType_toTheory_subset
    (p : T.CompleteType α) :
    p.toPartialType.toTheory ⊆ (p : L[[α]].Theory) := by
  intro φ
  simp only [PartialType.mem_toTheory, withSet, mem_union, LHom.mem_onTheory, mem_image_equiv,
    SetLike.mem_coe]
  rintro (⟨ψ,hψ,hψ'⟩ | h)
  · rw [← hψ']
    apply p.mem_of_models
    refine models_sentence_of_mem ?_
    exists ψ
  · simpa [toPartialType] using h

theorem equivSentence_mem_toPartialType_toTheory_iff
    (p : T.CompleteType α) (φ : L.Formula α) :
    Formula.equivSentence φ ∈ p.toPartialType.toTheory ↔
      Formula.equivSentence φ ∈ p := by
  constructor <;> intro h
  · exact p.toPartialType_toTheory_subset h
  · exact PartialType.mem_toTheory_of_mem (p.toPartialType) h

theorem toPartialType_toTheory_eq
    (p : T.CompleteType α) :
    p.toPartialType.toTheory = (p : L[[α]].Theory) := by
  ext φ
  simpa using
    p.equivSentence_mem_toPartialType_toTheory_iff (Formula.equivSentence.symm φ)

theorem toPartialType_toTheory_isMaximal
    (p : T.CompleteType α) :
    p.toPartialType.toTheory.IsMaximal := by
  simpa [p.toPartialType_toTheory_eq] using p.isMaximal

theorem equivSentence_mem_or_not_mem_toPartialType_toTheory
    (p : T.CompleteType α) (φ : L.Formula α) :
    Formula.equivSentence φ ∈ p.toPartialType.toTheory ∨
      (Formula.equivSentence φ).not ∈ p.toPartialType.toTheory := by
  exact p.toPartialType_toTheory_isMaximal.mem_or_not_mem _

theorem mem_or_not_mem_toPartialType
    (p : T.CompleteType α) (φ : L.Formula α) :
    φ ∈ p.toPartialType ∨ φ.not ∈ p.toPartialType := by
  change _ ∈ (p : L[[α]].Theory) ∨ _ ∈ (p : L[[α]].Theory)
  simpa [← toPartialType_toTheory_eq, mem_toTheory] using
    p.equivSentence_mem_or_not_mem_toPartialType_toTheory φ

theorem toPartialType_isMax
    (p : T.CompleteType α) :
    IsMax p.toPartialType := by
  intro q hpq φ hφ
  exact (p.mem_or_not_mem_toPartialType φ).resolve_right fun hφnot =>
    False.elim <| (q.not_mem_and_mem_not φ) ⟨hφ, hpq hφnot⟩

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]

theorem realizedBy_typeOf (v : α → M) :
    (T.typeOf v).toPartialType.RealizedBy v := by
  simp [PartialType.RealizedBy]

end CompleteType

namespace PartialType

theorem exists_modelType_realized_completeType
    (p : T.PartialType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, ∃ q ∈ T.realizedTypes M α,
      (p : Set (L.Formula α)) ⊆ q.toPartialType := by
  obtain ⟨M,⟨v,hv⟩⟩ := exists_modelType_isRealizedIn p
  exists M, T.typeOf v
  constructor <;> simp
  simpa [SetLike.le_def, RealizedBy] using hv

theorem exists_le_completeType (p : T.PartialType α) :
    ∃ q : T.CompleteType α, (p : Set (L.Formula α)) ⊆ q.toPartialType := by
  obtain ⟨M,q,hq,hpq⟩ := p.exists_modelType_realized_completeType
  aesop

end PartialType

end Theory

end Language

end FirstOrder
