import Mathlib.ModelTheory.Topology.Types
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sets.Closeds
import StabilityTheory.ModelTheory.Types

open Set TopologicalSpace FirstOrder.Language.Theory.CompleteType

namespace FirstOrder

namespace Language

namespace Theory

universe u v w w'

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

namespace CompleteType

/-- `typesWith φ` viewed as a closed set. -/
def toCloseds_typesWith (φ : L[[α]].Sentence) : Closeds (T.CompleteType α) :=
  ⟨typesWith (T := T) φ, CompleteType.isClosed_typesWith φ⟩

@[simp]
theorem coe_toCloseds_typesWith (φ : L[[α]].Sentence) :
    (toCloseds_typesWith (T := T) φ : Set (T.CompleteType α)) = typesWith (T := T) φ :=
  rfl

/-- `typesWith φ` viewed as a clopen set. -/
def toClopens_typesWith (φ : L[[α]].Sentence) : Clopens (T.CompleteType α) :=
  ⟨typesWith (T := T) φ, CompleteType.isClopen_typesWith φ⟩

@[simp]
theorem coe_toClopens_typesWith (φ : L[[α]].Sentence) :
    (toClopens_typesWith (T := T) φ : Set (T.CompleteType α)) = typesWith (T := T) φ :=
  rfl

/-- The type space of complete types is compact. -/
instance : CompactSpace (T.CompleteType α) := by
  classical
  constructor
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro F _
  refine ⟨⟨{φ | typesWith (T := T) φ ∈ F}, ?_, ?_⟩, trivial, ?_⟩
  · intro φ hφ
    exact F.mem_of_superset Filter.univ_mem (fun p _ => p.subset hφ)
  · rw [Theory.IsMaximal, Theory.isSatisfiable_iff_isFinitelySatisfiable]
    refine ⟨?_, ?_⟩
    · rw [Theory.IsFinitelySatisfiable]
      intro x hx
      have hx' : ∀ φ ∈ x, typesWith (T := T) φ ∈ (F : Filter (T.CompleteType α)) := by
        intro φ hφ
        exact hx hφ
      rw [← Filter.biInter_finset_mem x] at hx'
      obtain ⟨p, hp⟩ := F.nonempty_of_mem hx'
      have hsubset : (x : L[[α]].Theory) ⊆ (p : L[[α]].Theory) := by
        rwa [Set.mem_iInter₂] at hp
      exact Theory.IsSatisfiable.mono p.isMaximal.1 hsubset
    · intro φ
      simp only [mem_setOf_eq, typesWith_not]
      exact F.mem_or_compl_mem (typesWith (T := T) φ)
  · rw [nhds_generateFrom]
    apply le_iInf₂
    intro _ h
    rw [Filter.le_principal_iff]
    obtain ⟨_, rfl⟩ := h.2
    exact h.1

/-- Finite subcover extraction for covers by basic `typesWith` sets. -/
theorem finite_subcover_of_sUnion_eq_univ_typesWith
    {S : Set (L[[α]].Sentence)}
    (hS : ⋃₀ (typesWith (T := T) '' S) = (Set.univ : Set (T.CompleteType α))) :
    ∃ S₀ ⊆ S, S₀.Finite ∧
      ⋃₀ (typesWith (T := T) '' S₀) = (Set.univ : Set (T.CompleteType α)) := by
  obtain ⟨S₀, hS₀, hS₀fin, hcover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (T.CompleteType α))).elim_finite_subcover_image
      (b := S) (c := fun φ => typesWith (T := T) φ)
      (fun φ _ => CompleteType.isOpen_typesWith (T := T) φ)
      (by simpa [sUnion_image] using hS.symm.subset)
  refine ⟨S₀, hS₀, hS₀fin, ?_⟩
  exact Set.Subset.antisymm (subset_univ _) (by simpa [sUnion_image] using hcover)

/-- Each basic clopen `typesWith φ` is compact. -/
theorem isCompact_typesWith (φ : L[[α]].Sentence) :
    IsCompact (typesWith (T := T) φ) := by
  exact (CompleteType.isClosed_typesWith (T := T) φ).isCompact

/-- The type space of complete types is Hausdorff. -/
instance : T2Space (T.CompleteType α) := by
  infer_instance

section TypeOf

variable {M : Type w'} [TopologicalSpace M] [DiscreteTopology M]
variable [L.Structure M] [Nonempty M] [M ⊨ T]

/-- The map sending a tuple to its complete type is continuous for the product topology. -/
theorem continuous_typeOf :
    Continuous fun v : α → M => T.typeOf v := by
  classical
  rw [CompleteType.isTopologicalBasis_range_typesWith.continuous_iff]
  intro s hs
  rcases hs with ⟨φ, rfl⟩
  let ψ : L.Formula α := Formula.equivSentence.symm φ
  let U : Set (ψ.freeVarFinset → M) :=
    {w | Formula.Realize (ψ.restrictFreeVar id) w}
  have hU : IsOpen U := by
    simp [U]
  have hpre :
    ((fun v : α → M => T.typeOf v) ⁻¹' typesWith (T := T) φ) =
      (fun v : α → M => fun a : ψ.freeVarFinset => v a) ⁻¹' U := by
    ext v
    simp only [mem_preimage, mem_typesWith_iff, mem_typeOf, preimage_setOf_eq, mem_setOf_eq, U]
    change ψ.Realize v ↔ _
    simp [Formula.Realize, BoundedFormula.realize_restrictFreeVar]
  rw [hpre]
  exact hU.preimage
    (f := fun v : α → M => fun a : ψ.freeVarFinset => v a)
    (continuous_pi fun a : ψ.freeVarFinset => continuous_apply (a : α))

end TypeOf

end CompleteType

end Theory

end Language

end FirstOrder
